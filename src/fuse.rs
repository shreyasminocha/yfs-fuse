use fuser::{FileType, Filesystem, ReplyAttr, ReplyData, ReplyDirectory, ReplyEntry, Request};
use libc::ENOENT;
use std::ffi::OsStr;

use crate::yfs::{Inode, InodeType, YfsDisk, BLOCK_SIZE};

pub struct Yfs(pub YfsDisk);

impl Filesystem for Yfs {
    fn lookup(&mut self, _req: &Request, parent: u64, name: &OsStr, reply: ReplyEntry) {
        let parent_inode = self.0.read_inode(parent as i16);

        for entry in self.0.read_directory(parent_inode) {
            if entry.name.to_string() == name.to_string_lossy() {
                let entry_inode = self.0.read_inode(entry.inum);

                reply.entry(
                    &std::time::Duration::new(1, 0),
                    &inode_to_attr(entry.inum as u64, entry_inode),
                    1,
                );
                return;
            }
        }

        reply.error(ENOENT);
    }

    fn getattr(&mut self, _req: &Request, ino: u64, reply: ReplyAttr) {
        let inode = self.0.read_inode(ino as i16);
        reply.attr(&std::time::Duration::new(1, 0), &inode_to_attr(ino, inode));
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
        let inode = self.0.read_inode(ino as i16);
        let data = self.0.read_file(inode, offset as usize, size as usize);
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
        let inode = self.0.read_inode(ino as i16);
        let entries = self.0.read_directory(inode);

        for (i, entry) in entries.iter().enumerate().skip(offset as usize) {
            let entry_inode = self.0.read_inode(entry.inum);

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

fn inode_to_attr(ino: u64, inode: Inode) -> fuser::FileAttr {
    fuser::FileAttr {
        ino,
        size: inode.size as u64,
        blocks: (inode.size as u64 + BLOCK_SIZE as u64 - 1) / BLOCK_SIZE as u64,
        atime: std::time::UNIX_EPOCH,
        mtime: std::time::UNIX_EPOCH,
        ctime: std::time::UNIX_EPOCH,
        crtime: std::time::UNIX_EPOCH,
        kind: match inode.type_ {
            InodeType::Directory => FileType::Directory,
            InodeType::Regular => FileType::RegularFile,
            InodeType::Free => panic!(),
            _ => unreachable!(),
        },
        perm: 0o755,
        nlink: inode.nlink as u32,
        uid: 0,
        gid: 0,
        rdev: 0,
        flags: 0,
        blksize: BLOCK_SIZE as u32,
    }
}
