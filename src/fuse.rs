use std::ffi::{CStr, CString, OsStr};
use std::ops::ControlFlow;
use std::os::unix::ffi::OsStrExt;
use std::path::Path;
use std::time::Duration;

use anyhow::{anyhow, ensure, Result};
use fuser::{
    FileAttr, FileType, Filesystem, ReplyAttr, ReplyCreate, ReplyData, ReplyDirectory, ReplyEmpty,
    ReplyEntry, ReplyOpen, ReplyStatfs, ReplyWrite, Request,
};
use libc::{EINVAL, ENOENT};
use log::warn;

use crate::{
    disk_format::{
        block::BLOCK_SIZE,
        directory_entry::{DirectoryEntry, MAX_NAME_LEN},
        inode::InodeType,
    },
    storage::YfsStorage,
    yfs::{InodeNumber, Yfs},
};

pub struct YfsFs<S: YfsStorage> {
    yfs: Yfs<S>,
    first_free_handle: u64,
}

impl<S: YfsStorage> YfsFs<S> {
    const TTL: Duration = Duration::new(1, 0);
    const GENERATION: u64 = 1;

    pub fn new(yfs: Yfs<S>) -> Result<YfsFs<S>> {
        Ok(YfsFs {
            yfs,
            first_free_handle: 0,
        })
    }

    /// Sets uid and gid to 0. Sets permissions to 755.
    fn get_attributes(&self, inum: InodeNumber) -> Result<Option<FileAttr>> {
        let inode = self.yfs.read_inode(inum)?;

        if inode.type_ == InodeType::Free {
            return Ok(None);
        }

        let time_metadata = self.yfs.storage.time_metadata().unwrap_or_default();
        let ownership_metadata = self.yfs.storage.ownership_metadata().unwrap_or_default();

        Ok(Some(FileAttr {
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
                InodeType::Symlink => FileType::Symlink,
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

    fn set_attributes(&mut self, inum: InodeNumber, size: Option<u64>) -> Result<FileAttr> {
        if let Some(new_size) = size {
            self.yfs
                .update_inode(inum, |inode| inode.size = new_size as i32)?;
        }

        self.get_attributes(inum)
            .map(|attr| attr.expect("we just successfully updated its size, so it must exist"))
    }

    fn open_file(&mut self, _inum: InodeNumber) -> u64 {
        self.assign_file_handle()
    }

    fn open_directory(&mut self, _inum: InodeNumber) -> u64 {
        self.assign_file_handle()
    }

    fn lookup_entry(&self, parent_inum: InodeNumber, name: &CStr) -> Result<Option<FileAttr>> {
        let entry_inum = self.yfs.lookup_entry(parent_inum, name)?;
        let attr = match entry_inum {
            None => None,
            Some(inum) => Some(
                self.get_attributes(inum)?
                    .ok_or(anyhow!("entry points to inum without attributes: {}", inum))?,
            ),
        };

        Ok(attr)
    }

    fn read_file(&self, inum: InodeNumber, offset: usize, size: usize) -> Result<Vec<u8>> {
        self.yfs.read_file(inum, offset, size)
    }

    fn read_directory(
        &self,
        inum: InodeNumber,
        offset: usize,
    ) -> Result<Vec<(DirectoryEntry, InodeType)>> {
        let entries = self.yfs.read_directory(inum)?;
        let mut directory_contents = vec![];

        // this can't be a `filter_map` because of the potential error in reading the inode
        for entry in entries.into_iter().skip(offset) {
            let entry_inum = entry.inum as InodeNumber;
            let entry_inode = self.yfs.read_inode(entry_inum)?;

            if entry_inode.type_ == InodeType::Free {
                warn!("directory includes free entry: {inum}");
                continue;
            }

            directory_contents.push((entry, entry_inode.type_));
        }

        Ok(directory_contents)
    }

    fn write_file(&mut self, inum: InodeNumber, offset: usize, data: &[u8]) -> Result<u32> {
        let write_len = self.yfs.write_file(inum, offset, data)?;
        Ok(write_len as u32)
    }

    fn create_file(&mut self, parent_inum: InodeNumber, name: &CStr) -> Result<FileAttr> {
        let new_inum = self.yfs.create_file(parent_inum, name)?;
        let attr = self
            .get_attributes(new_inum)?
            .expect("we just created the file");

        Ok(attr)
    }

    fn create_directory(&mut self, parent_inum: InodeNumber, name: &CStr) -> Result<FileAttr> {
        let new_inum = self.yfs.create_directory(parent_inum, name)?;

        let attr = self
            .get_attributes(new_inum)?
            .expect("we just created the directory");

        Ok(attr)
    }

    fn remove_directory(&mut self, parent_inum: InodeNumber, name: &CStr) -> Result<()> {
        let _ = self.yfs.remove_directory(parent_inum, name)?;

        Ok(())
    }

    fn create_hard_link(
        &mut self,
        parent_inum: InodeNumber,
        name: &CStr,
        inum: InodeNumber,
    ) -> Result<FileAttr> {
        self.yfs.create_hard_link(parent_inum, name, inum)?;

        let attr = self
            .get_attributes(inum)?
            .expect("we successfully created a link to the inode, so it must exist");

        Ok(attr)
    }

    fn remove_hard_link(&mut self, parent_inum: InodeNumber, name: &CStr) -> Result<()> {
        let entry_inum = self.yfs.remove_hard_link(parent_inum, name)?;

        let attr = self.get_attributes(entry_inum)?;
        ensure!(attr.is_none(), "we just removed the entry");

        Ok(())
    }

    fn assign_file_handle(&mut self) -> u64 {
        let assigned = self.first_free_handle;
        self.first_free_handle += 1;

        assigned
    }

    fn rename_entry(
        &mut self,
        parent_inum: InodeNumber,
        name: &CStr,
        new_parent_inum: InodeNumber,
        new_name: &CStr,
    ) -> Result<()> {
        self.yfs
            .rename(parent_inum, name, new_parent_inum, new_name)
    }

    fn create_symbolic_link(
        &mut self,
        parent_inum: InodeNumber,
        name: &CStr,
        link: &CStr,
    ) -> Result<FileAttr> {
        let new_inum = self.yfs.create_symbolic_link(parent_inum, name, link)?;

        let attr = self
            .get_attributes(new_inum)?
            .expect("we just created the symbolic link");

        Ok(attr)
    }

    fn read_symbolic_link(&mut self, inum: InodeNumber) -> Result<Vec<u8>> {
        self.yfs.read_symbolic_link(inum)
    }
}

impl<S: YfsStorage> Filesystem for YfsFs<S> {
    fn statfs(&mut self, _req: &Request<'_>, _ino: u64, reply: ReplyStatfs) {
        let num_free_blocks = self.yfs.num_free_blocks();
        let num_free_inodes = self.yfs.num_free_inodes();

        reply.statfs(
            self.yfs.num_blocks as u64,
            num_free_blocks as u64,
            num_free_blocks as u64,
            self.yfs.num_inodes as u64,
            num_free_inodes as u64,
            BLOCK_SIZE as u32,
            MAX_NAME_LEN as u32,
            BLOCK_SIZE as u32,
        );
    }

    fn lookup(&mut self, _req: &Request, parent: u64, name: &OsStr, reply: ReplyEntry) {
        let Ok(name) = CString::new(name.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        if let Ok(Some(attr)) = self.lookup_entry(parent as InodeNumber, &name) {
            reply.entry(&Self::TTL, &attr, Self::GENERATION);
        } else {
            reply.error(ENOENT);
        }
    }

    fn open(&mut self, _req: &Request<'_>, ino: u64, flags: i32, reply: ReplyOpen) {
        let handle = self.open_file(ino as InodeNumber);
        reply.opened(handle, flags as u32);
    }

    fn opendir(&mut self, _req: &Request<'_>, ino: u64, flags: i32, reply: ReplyOpen) {
        let handle = self.open_directory(ino as InodeNumber);
        reply.opened(handle, flags as u32);
    }

    fn getattr(&mut self, _req: &Request, ino: u64, reply: ReplyAttr) {
        if let Ok(Some(attr)) = self.get_attributes(ino as InodeNumber) {
            reply.attr(&Self::TTL, &attr);
        } else {
            reply.error(EINVAL);
        }
    }

    fn setattr(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        _mode: Option<u32>,
        _uid: Option<u32>,
        _gid: Option<u32>,
        size: Option<u64>,
        _atime: Option<fuser::TimeOrNow>,
        _mtime: Option<fuser::TimeOrNow>,
        _ctime: Option<std::time::SystemTime>,
        _fh: Option<u64>,
        _crtime: Option<std::time::SystemTime>,
        _chgtime: Option<std::time::SystemTime>,
        _bkuptime: Option<std::time::SystemTime>,
        _flags: Option<u32>,
        reply: ReplyAttr,
    ) {
        if let Ok(attr) = self.set_attributes(ino as InodeNumber, size) {
            reply.attr(&Self::TTL, &attr);
        } else {
            reply.error(ENOENT);
        }
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
        if let Ok(data) = self.read_file(ino as InodeNumber, offset as usize, size as usize) {
            reply.data(&data);
        } else {
            reply.error(ENOENT);
        }
    }

    fn readdir(
        &mut self,
        _req: &Request,
        ino: u64,
        _fh: u64,
        offset: i64,
        mut reply: ReplyDirectory,
    ) {
        let Ok(entries) = self.read_directory(ino as InodeNumber, offset as usize) else {
            reply.error(ENOENT);
            return;
        };

        entries
            .into_iter()
            .enumerate()
            .try_for_each(|(i, (entry, inode_type))| {
                let file_type = match inode_type {
                    InodeType::Directory => FileType::Directory,
                    InodeType::Regular => FileType::RegularFile,
                    InodeType::Symlink => FileType::Symlink,
                    InodeType::Free => {
                        unreachable!("we filtered these in `self.read_directory`")
                    }
                };

                let is_buffer_full = reply.add(
                    entry.inum as u64,
                    (i + 1) as i64,
                    file_type,
                    entry.name.to_string(),
                );

                if is_buffer_full {
                    return ControlFlow::Break(());
                }

                ControlFlow::Continue(())
            });

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
        reply: ReplyWrite,
    ) {
        if let Ok(write_len) = self.write_file(ino as InodeNumber, offset as usize, data) {
            reply.written(write_len);
        } else {
            reply.error(ENOENT);
        }
    }

    fn create(
        &mut self,
        _req: &Request<'_>,
        parent: u64,
        name: &OsStr,
        _mode: u32,
        _umask: u32,
        flags: i32,
        reply: ReplyCreate,
    ) {
        let Ok(name) = CString::new(name.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        if let Ok(attr) = self.create_file(parent as InodeNumber, &name) {
            reply.created(
                &Self::TTL,
                &attr,
                Self::GENERATION,
                self.assign_file_handle(),
                flags as u32,
            );
        } else {
            reply.error(EINVAL);
        }
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

        if let Ok(attr) = self.create_directory(parent as InodeNumber, &name) {
            reply.entry(&Self::TTL, &attr, Self::GENERATION);
        } else {
            reply.error(EINVAL);
        }
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

        if let Ok(attr) = self.create_hard_link(newparent as InodeNumber, &name, ino as InodeNumber)
        {
            reply.entry(&Self::TTL, &attr, Self::GENERATION);
        } else {
            reply.error(EINVAL);
        }
    }

    fn unlink(&mut self, _req: &Request<'_>, parent: u64, name: &OsStr, reply: ReplyEmpty) {
        let Ok(name) = CString::new(name.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        if self.remove_hard_link(parent as InodeNumber, &name).is_ok() {
            reply.ok();
        } else {
            reply.error(EINVAL);
        }
    }

    fn rmdir(&mut self, _req: &Request<'_>, parent: u64, name: &OsStr, reply: ReplyEmpty) {
        let Ok(name) = CString::new(name.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        if self.remove_directory(parent as InodeNumber, &name).is_ok() {
            reply.ok();
        } else {
            reply.error(EINVAL);
        }
    }

    fn rename(
        &mut self,
        _req: &Request<'_>,
        parent: u64,
        name: &OsStr,
        newparent: u64,
        newname: &OsStr,
        _flags: u32,
        reply: ReplyEmpty,
    ) {
        let Ok(name) = CString::new(name.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        let Ok(new_name) = CString::new(newname.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        if self
            .rename_entry(
                parent as InodeNumber,
                &name,
                newparent as InodeNumber,
                &new_name,
            )
            .is_ok()
        {
            reply.ok();
        } else {
            reply.error(EINVAL);
        }
    }

    fn symlink(
        &mut self,
        _req: &Request<'_>,
        parent: u64,
        name: &OsStr,
        link: &Path,
        reply: ReplyEntry,
    ) {
        let Ok(name) = CString::new(name.as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        let Ok(link) = CString::new(link.as_os_str().as_bytes()) else {
            reply.error(EINVAL);
            return;
        };

        if let Ok(attr) = self.create_symbolic_link(parent as InodeNumber, &name, &link) {
            reply.entry(&Self::TTL, &attr, Self::GENERATION);
        } else {
            reply.error(EINVAL);
        }
    }

    fn readlink(&mut self, _req: &Request<'_>, ino: u64, reply: ReplyData) {
        if let Ok(data) = self.read_symbolic_link(ino as InodeNumber) {
            reply.data(&data);
        } else {
            reply.error(EINVAL);
        }
    }
}
