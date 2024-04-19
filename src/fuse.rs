use fuser::{FileType, Filesystem, ReplyAttr, ReplyData, ReplyDirectory, ReplyEntry, Request};
use libc::{EINVAL, ENOENT};
use std::ffi::OsStr;

use crate::disk_format::{Inode, InodeType, BLOCK_SIZE};
use crate::yfs::{InodeNumber, YfsDisk};

pub struct Yfs(pub YfsDisk);

impl Yfs {
    /// Converts an inode to a fuse FileAttr.
    ///
    /// Sets uid and gid to 0. Sets permissions to 755.
    fn inode_to_attr(&self, ino: InodeNumber, inode: Inode) -> fuser::FileAttr {
        let time_metadata = self.0.time_metadata().unwrap_or_default();
        let ownership_metadata = self.0.ownership_metadata().unwrap_or_default();

        fuser::FileAttr {
            ino: ino as u64,
            size: inode.size as u64,
            blocks: (inode.size as u64 + BLOCK_SIZE as u64 - 1) / BLOCK_SIZE as u64,
            atime: time_metadata.atime,
            mtime: time_metadata.mtime,
            ctime: time_metadata.mtime,
            crtime: time_metadata.crtime,
            kind: match inode.type_ {
                InodeType::Directory => FileType::Directory,
                InodeType::Regular => FileType::RegularFile,
                InodeType::Free => panic!(),
                _ => unreachable!(),
            },
            perm: 0o755,
            nlink: inode.nlink as u32,
            uid: ownership_metadata.uid,
            gid: ownership_metadata.gid,
            rdev: 0,
            flags: 0,
            blksize: BLOCK_SIZE as u32,
        }
    }
}

impl Filesystem for Yfs {
    fn lookup(&mut self, _req: &Request, parent: u64, name: &OsStr, reply: ReplyEntry) {
        let Ok(parent_inum) = parent.try_into() else {
            reply.error(EINVAL);
            return;
        };

        let Ok(parent_inode) = self.0.read_inode(parent_inum) else {
            reply.error(ENOENT);
            return;
        };

        let Ok(entries) = self.0.read_directory(parent_inode) else {
            reply.error(ENOENT);
            return;
        };

        for entry in entries {
            if entry.name.to_string() == name.to_string_lossy() {
                let Ok(entry_inum) = entry.inum.try_into() else {
                    reply.error(EINVAL);
                    return;
                };

                let Ok(entry_inode) = self.0.read_inode(entry_inum) else {
                    reply.error(ENOENT);
                    return;
                };

                reply.entry(
                    &std::time::Duration::new(1, 0),
                    &self.inode_to_attr(entry_inum, entry_inode),
                    1,
                );
                return;
            }
        }

        reply.error(ENOENT);
    }

    fn getattr(&mut self, _req: &Request, ino: u64, reply: ReplyAttr) {
        let Ok(inum) = ino.try_into() else {
            reply.error(EINVAL);
            return;
        };

        let Ok(inode) = self.0.read_inode(inum) else {
            reply.error(ENOENT);
            return;
        };

        reply.attr(
            &std::time::Duration::new(1, 0),
            &self.inode_to_attr(inum, inode),
        );
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

        let Ok(inode) = self.0.read_inode(inum) else {
            reply.error(ENOENT);
            return;
        };

        let Ok(data) = self.0.read_file(inode, offset as usize, size as usize) else {
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

        let Ok(inode) = self.0.read_inode(inum) else {
            reply.error(ENOENT);
            return;
        };

        let Ok(entries) = self.0.read_directory(inode) else {
            reply.error(ENOENT);
            return;
        };

        for (i, entry) in entries.iter().enumerate().skip(offset as usize) {
            let Ok(entry_inum) = entry.inum.try_into() else {
                reply.error(EINVAL);
                return;
            };

            let Ok(entry_inode) = self.0.read_inode(entry_inum) else {
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
}
