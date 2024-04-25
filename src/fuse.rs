use anyhow::Result;
use fuser::{
    FileType, Filesystem, ReplyAttr, ReplyData, ReplyDirectory, ReplyEntry, Request, TimeOrNow,
};
use libc::{EINVAL, ENOENT};
use log::debug;
use std::ffi::OsStr;
use std::time::SystemTime;

use crate::disk_format::{InodeType, BLOCK_SIZE};
use crate::yfs::{InodeNumber, YfsDisk};

pub struct Yfs {
    yfs_disk: YfsDisk,
    attributes: Vec<Option<fuser::FileAttr>>,
    first_free_handle: u64,
}

impl Yfs {
    pub fn new(yfs_disk: YfsDisk) -> Result<Yfs> {
        let mut attributes = vec![None];

        for inum in 1..=yfs_disk.num_inodes {
            let inode = yfs_disk.read_inode(inum as u16)?;

            if inode.type_ == InodeType::Free {
                debug!("free inode #{inum}");

                // todo: remove temporary hack
                // attributes.push(None);
                attributes.push(Some(Self::inode_to_attr(&yfs_disk, inum as InodeNumber)?));
            } else {
                attributes.push(Some(Self::inode_to_attr(&yfs_disk, inum as InodeNumber)?));
            }
        }

        Ok(Yfs {
            yfs_disk,
            attributes,
            first_free_handle: 0,
        })
    }

    /// Converts an inode to a fuse FileAttr.
    ///
    /// Sets uid and gid to 0. Sets permissions to 755.
    fn inode_to_attr(yfs_disk: &YfsDisk, inum: InodeNumber) -> Result<fuser::FileAttr> {
        let inode = yfs_disk.read_inode(inum)?;

        let time_metadata = yfs_disk.time_metadata().unwrap_or_default();
        let ownership_metadata = yfs_disk.ownership_metadata().unwrap_or_default();

        Ok(fuser::FileAttr {
            ino: inum as u64,
            size: inode.size as u64,
            blocks: inode.size.div_ceil(BLOCK_SIZE as i32) as u64,
            atime: time_metadata.atime,
            mtime: time_metadata.mtime,
            ctime: time_metadata.mtime,
            crtime: time_metadata.crtime,
            kind: match inode.type_ {
                InodeType::Directory => FileType::Directory,
                InodeType::Regular => FileType::RegularFile,
                // todo: remove temporary hack
                InodeType::Free => FileType::RegularFile,
                _ => unreachable!(),
            },
            perm: 0o755,
            nlink: inode.nlink as u32,
            uid: ownership_metadata.uid,
            gid: ownership_metadata.gid,
            rdev: 0,
            flags: 0,
            blksize: BLOCK_SIZE as u32,
        })
    }
}

impl Filesystem for Yfs {
    fn lookup(&mut self, _req: &Request, parent: u64, name: &OsStr, reply: ReplyEntry) {
        let Ok(parent_inum) = parent.try_into() else {
            reply.error(EINVAL);
            return;
        };

        let Ok(entries) = self.yfs_disk.read_directory(parent_inum) else {
            reply.error(ENOENT);
            return;
        };

        for entry in entries {
            if entry.name.to_string() == name.to_string_lossy() {
                let Some(attr) = self.attributes[entry.inum as usize] else {
                    reply.error(ENOENT);
                    return;
                };

                reply.entry(&std::time::Duration::new(1, 0), &attr, 1);
                return;
            }
        }

        reply.error(ENOENT);
    }

    fn open(&mut self, _req: &Request<'_>, _ino: u64, flags: i32, reply: fuser::ReplyOpen) {
        reply.opened(self.first_free_handle, flags as u32);
        self.first_free_handle += 1;
    }

    fn opendir(&mut self, _req: &Request<'_>, _ino: u64, flags: i32, reply: fuser::ReplyOpen) {
        reply.opened(self.first_free_handle, flags as u32);
        self.first_free_handle += 1;
    }

    fn getattr(&mut self, _req: &Request, ino: u64, reply: ReplyAttr) {
        let Some(attr) = self.attributes[ino as usize] else {
            reply.error(EINVAL);
            return;
        };

        reply.attr(&std::time::Duration::new(1, 0), &attr);
    }

    fn setattr(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        _mode: Option<u32>,
        _uid: Option<u32>,
        _gid: Option<u32>,
        size: Option<u64>,
        atime: Option<fuser::TimeOrNow>,
        mtime: Option<fuser::TimeOrNow>,
        ctime: Option<std::time::SystemTime>,
        _fh: Option<u64>,
        _crtime: Option<std::time::SystemTime>,
        _chgtime: Option<std::time::SystemTime>,
        _bkuptime: Option<std::time::SystemTime>,
        _flags: Option<u32>,
        reply: ReplyAttr,
    ) {
        let Some(attr) = &mut self.attributes[ino as usize] else {
            reply.error(ENOENT);
            return;
        };

        attr.size = size.unwrap_or(attr.size);

        attr.atime = atime
            .map(|t| match t {
                TimeOrNow::SpecificTime(time) => time,
                TimeOrNow::Now => SystemTime::now(),
            })
            .unwrap_or(attr.atime);
        attr.mtime = mtime
            .map(|t| match t {
                TimeOrNow::SpecificTime(time) => time,
                TimeOrNow::Now => SystemTime::now(),
            })
            .unwrap_or(attr.mtime);
        attr.ctime = ctime.unwrap_or(attr.ctime);

        reply.attr(&std::time::Duration::new(1, 0), attr);
    }

    fn read(
        &mut self,
        _req: &Request,
        ino: u64,
        _fh: u64,
        offset: i64,
        size: u32,
        _flags: i32,
        _lock: Option<u64>,
        reply: ReplyData,
    ) {
        let Ok(inum) = ino.try_into() else {
            reply.error(EINVAL);
            return;
        };

        let Ok(data) = self
            .yfs_disk
            .read_file(inum, offset as usize, size as usize)
        else {
            reply.error(ENOENT);
            return;
        };

        reply.data(&data);
    }

    fn readdir(
        &mut self,
        _req: &Request,
        ino: u64,
        _fh: u64,
        offset: i64,
        mut reply: ReplyDirectory,
    ) {
        let Ok(inum) = ino.try_into() else {
            reply.error(EINVAL);
            return;
        };

        let Ok(entries) = self.yfs_disk.read_directory(inum) else {
            reply.error(ENOENT);
            return;
        };

        for (i, entry) in entries.iter().enumerate().skip(offset as usize) {
            let Ok(entry_inum) = entry.inum.try_into() else {
                reply.error(EINVAL);
                return;
            };

            let Ok(entry_inode) = self.yfs_disk.read_inode(entry_inum) else {
                reply.error(ENOENT);
                return;
            };

            let entry_type = match entry_inode.type_ {
                InodeType::Directory => FileType::Directory,
                InodeType::Regular => FileType::RegularFile,
                InodeType::Free => continue,
                _ => unreachable!(),
            };

            if reply.add(
                entry.inum as u64,
                (i + 1) as i64,
                entry_type,
                entry.name.to_string(),
            ) {
                break;
            }
        }

        reply.ok();
    }

    fn write(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        _fh: u64,
        offset: i64,
        data: &[u8],
        _write_flags: u32,
        _flags: i32,
        _lock_owner: Option<u64>,
        reply: fuser::ReplyWrite,
    ) {
        let Ok(inum) = ino.try_into() else {
            reply.error(EINVAL);
            return;
        };

        let Ok(write_len) = self.yfs_disk.write_file(inum, offset as usize, data) else {
            reply.error(ENOENT);
            return;
        };

        let Ok(attr) = Self::inode_to_attr(&self.yfs_disk, inum) else {
            reply.error(ENOENT);
            return;
        };

        self.attributes[ino as usize] = Some(attr);

        reply.written(write_len as u32);
    }
}
