use anyhow::Result;
use fuser::{
    FileType, Filesystem, ReplyAttr, ReplyData, ReplyDirectory, ReplyEntry, Request, TimeOrNow,
};
use libc::{EINVAL, ENOENT};
use std::ffi::{CString, OsStr};
use std::os::unix::ffi::OsStrExt;
use std::time::{Duration, SystemTime};

use crate::disk_format::{block::BLOCK_SIZE, inode::InodeType};
use crate::storage::YfsStorage;
use crate::yfs::{InodeNumber, Yfs};

pub struct YfsFs<S: YfsStorage> {
    yfs: Yfs<S>,
    attributes: Vec<Option<fuser::FileAttr>>,
    first_free_handle: u64,
}

impl<S: YfsStorage> YfsFs<S> {
    const TTL: Duration = Duration::new(1, 0);
    const GENERATION: u64 = 1;

    pub fn new(yfs: Yfs<S>) -> Result<YfsFs<S>> {
        let mut attributes = vec![None];

        for inum in 1..=yfs.num_inodes {
            attributes.push(Self::inode_to_attr(&yfs, inum as InodeNumber)?);
        }

        Ok(YfsFs {
            yfs,
            attributes,
            first_free_handle: 0,
        })
    }

    /// Converts an inode to a fuse FileAttr.
    ///
    /// Sets uid and gid to 0. Sets permissions to 755.
    fn inode_to_attr(yfs: &Yfs<S>, inum: InodeNumber) -> Result<Option<fuser::FileAttr>> {
        let inode = yfs.read_inode(inum)?;

        if inode.type_ == InodeType::Free {
            return Ok(None);
        }

        let time_metadata = yfs.storage.time_metadata().unwrap_or_default();
        let ownership_metadata = yfs.storage.ownership_metadata().unwrap_or_default();

        Ok(Some(fuser::FileAttr {
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
                InodeType::Symlink => unimplemented!("symlink support is unimplemented"),
                InodeType::Free => unreachable!("we handle this case above"),
            },
            perm: 0o755,
            nlink: inode.nlink as u32,
            uid: ownership_metadata.uid,
            gid: ownership_metadata.gid,
            rdev: 0,
            flags: 0,
            blksize: BLOCK_SIZE as u32,
        }))
    }

    fn assign_file_handle(&mut self) -> u64 {
        let assigned = self.first_free_handle;
        self.first_free_handle += 1;

        assigned
    }
}

impl<S: YfsStorage> Filesystem for YfsFs<S> {
    fn lookup(&mut self, _req: &Request, parent: u64, name: &OsStr, reply: ReplyEntry) {
        let Ok(parent_inum) = parent.try_into() else {
            reply.error(EINVAL);
            return;
        };

        let Ok(entries) = self.yfs.read_directory(parent_inum) else {
            reply.error(ENOENT);
            return;
        };

        for entry in entries {
            if entry.name.to_string() == name.to_string_lossy() {
                let Some(attr) = self.attributes[entry.inum as usize] else {
                    reply.error(ENOENT);
                    return;
                };

                reply.entry(&Self::TTL, &attr, Self::GENERATION);
                return;
            }
        }

        reply.error(ENOENT);
    }

    fn open(&mut self, _req: &Request<'_>, _ino: u64, flags: i32, reply: fuser::ReplyOpen) {
        reply.opened(self.assign_file_handle(), flags as u32);
    }

    fn opendir(&mut self, _req: &Request<'_>, _ino: u64, flags: i32, reply: fuser::ReplyOpen) {
        reply.opened(self.assign_file_handle(), flags as u32);
    }

    fn getattr(&mut self, _req: &Request, ino: u64, reply: ReplyAttr) {
        let Some(attr) = self.attributes[ino as usize] else {
            reply.error(EINVAL);
            return;
        };

        reply.attr(&Self::TTL, &attr);
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

        if let Some(new_size) = size {
            let Ok(mut inode) = self.yfs.read_inode(ino as InodeNumber) else {
                reply.error(ENOENT);
                return;
            };

            inode.size = new_size as i32;
            let Ok(_) = self.yfs.write_inode(ino as InodeNumber, inode) else {
                reply.error(ENOENT);
                return;
            };

            attr.size = new_size;
        }

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

        reply.attr(&Self::TTL, attr);
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

        let Ok(data) = self.yfs.read_file(inum, offset as usize, size as usize) else {
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

        let Ok(entries) = self.yfs.read_directory(inum) else {
            reply.error(ENOENT);
            return;
        };

        for (i, entry) in entries.iter().enumerate().skip(offset as usize) {
            let Ok(entry_inum) = entry.inum.try_into() else {
                reply.error(EINVAL);
                return;
            };

            let Ok(entry_inode) = self.yfs.read_inode(entry_inum) else {
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

        let Ok(write_len) = self.yfs.write_file(inum, offset as usize, data) else {
            reply.error(ENOENT);
            return;
        };

        let Ok(attr) = Self::inode_to_attr(&self.yfs, inum) else {
            reply.error(ENOENT);
            return;
        };

        self.attributes[ino as usize] = attr;

        reply.written(write_len as u32);
    }

    fn create(
        &mut self,
        _req: &Request<'_>,
        parent: u64,
        name: &OsStr,
        _mode: u32,
        _umask: u32,
        flags: i32,
        reply: fuser::ReplyCreate,
    ) {
        let Ok(name) = CString::new(name.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        let Ok(new_inum) = self.yfs.create_file(parent as InodeNumber, &name) else {
            reply.error(EINVAL);
            return;
        };

        let Ok(attr) = Self::inode_to_attr(&self.yfs, new_inum) else {
            reply.error(ENOENT);
            return;
        };

        self.attributes[new_inum as usize] = attr;

        reply.created(
            &Self::TTL,
            &attr.expect("we just created the inode"),
            Self::GENERATION,
            self.assign_file_handle(),
            flags as u32,
        );
    }

    fn mkdir(
        &mut self,
        _req: &Request<'_>,
        parent: u64,
        name: &OsStr,
        _mode: u32,
        _umask: u32,
        reply: ReplyEntry,
    ) {
        let Ok(name) = CString::new(name.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        let Ok(new_inum) = self.yfs.create_directory(parent as InodeNumber, &name) else {
            reply.error(EINVAL);
            return;
        };

        let Ok(attr) = Self::inode_to_attr(&self.yfs, new_inum) else {
            reply.error(ENOENT);
            return;
        };
        self.attributes[new_inum as usize] = attr;

        let Ok(parent_attr) = Self::inode_to_attr(&self.yfs, parent as InodeNumber) else {
            reply.error(ENOENT);
            return;
        };
        self.attributes[parent as usize] = parent_attr;

        reply.entry(
            &Self::TTL,
            &attr.expect("we just created the directory"),
            Self::GENERATION,
        );
    }

    fn link(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        newparent: u64,
        newname: &OsStr,
        reply: ReplyEntry,
    ) {
        let Ok(name) = CString::new(newname.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        let Ok(_) = self
            .yfs
            .create_hard_link(newparent as InodeNumber, &name, ino as InodeNumber)
        else {
            reply.error(EINVAL);
            return;
        };

        // we update the attributes to reflect the new `nlink`
        let Ok(attr) = Self::inode_to_attr(&self.yfs, ino as InodeNumber) else {
            reply.error(ENOENT);
            return;
        };
        self.attributes[ino as usize] = attr;

        reply.entry(
            &Self::TTL,
            &attr.expect("we successfully created a link to the inode, so it must exist"),
            Self::GENERATION,
        );
    }

    fn unlink(&mut self, _req: &Request<'_>, parent: u64, name: &OsStr, reply: fuser::ReplyEmpty) {
        let Ok(name) = CString::new(name.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        let Ok(entry_inum) = self.yfs.remove_hard_link(parent as InodeNumber, &name) else {
            reply.error(EINVAL);
            return;
        };

        // we update the attributes to reflect the new `nlink`
        let Ok(attr) = Self::inode_to_attr(&self.yfs, entry_inum as InodeNumber) else {
            reply.error(ENOENT);
            return;
        };
        self.attributes[entry_inum as usize] = attr;

        reply.ok();
    }
}
