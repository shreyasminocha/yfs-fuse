use std::ffi::{CStr, CString, OsStr};
use std::ops::ControlFlow;
use std::os::unix::ffi::OsStrExt;
use std::time::{Duration, SystemTime};

use anyhow::{anyhow, ensure, Result};
use fuser::{
    FileAttr, FileType, Filesystem, ReplyAttr, ReplyCreate, ReplyData, ReplyDirectory, ReplyEmpty,
    ReplyEntry, ReplyOpen, ReplyWrite, Request, TimeOrNow,
};
use libc::{EINVAL, ENOENT};
use log::warn;

use crate::{
    disk_format::{block::BLOCK_SIZE, directory_entry::DirectoryEntry, inode::InodeType},
    storage::YfsStorage,
    yfs::{InodeNumber, Yfs},
};

pub struct YfsFs<S: YfsStorage> {
    yfs: Yfs<S>,
    attributes: Vec<Option<FileAttr>>,
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

    fn get_attributes(&self, inum: InodeNumber) -> Option<FileAttr> {
        self.attributes[inum as usize]
    }

    fn set_attributes(
        &mut self,
        inum: InodeNumber,
        size: Option<u64>,
        atime: Option<fuser::TimeOrNow>,
        mtime: Option<fuser::TimeOrNow>,
        ctime: Option<std::time::SystemTime>,
    ) -> Result<FileAttr> {
        let attr =
            &mut self.attributes[inum as usize].ok_or(anyhow!("unable to access attributes"))?;

        if let Some(new_size) = size {
            let mut inode = self.yfs.read_inode(inum)?;
            inode.size = new_size as i32;
            self.yfs.write_inode(inum, inode)?;

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

        Ok(*attr)
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
                self.get_attributes(inum)
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

        let attr = Self::inode_to_attr(&self.yfs, inum)?;
        self.attributes[inum as usize] = attr;

        Ok(write_len as u32)
    }

    fn create_file(&mut self, parent_inum: InodeNumber, name: &CStr) -> Result<FileAttr> {
        let new_inum = self.yfs.create_file(parent_inum, name)?;

        let attr = Self::inode_to_attr(&self.yfs, new_inum)?;
        self.attributes[new_inum as usize] = attr;

        Ok(attr.expect("we just created the file"))
    }

    fn create_directory(&mut self, parent_inum: InodeNumber, name: &CStr) -> Result<FileAttr> {
        let new_inum = self.yfs.create_directory(parent_inum, name)?;

        let attr = Self::inode_to_attr(&self.yfs, new_inum)?;
        self.attributes[new_inum as usize] = attr;

        let parent_attr = Self::inode_to_attr(&self.yfs, parent_inum)?;
        self.attributes[parent_inum as usize] = parent_attr;

        Ok(attr.expect("we just created the directory"))
    }

    fn create_hard_link(
        &mut self,
        parent_inum: InodeNumber,
        name: &CStr,
        inum: InodeNumber,
    ) -> Result<FileAttr> {
        self.yfs.create_hard_link(parent_inum, name, inum)?;

        // we update the attributes to reflect the new `nlink`
        let attr = Self::inode_to_attr(&self.yfs, inum)?;
        self.attributes[inum as usize] = attr;

        Ok(attr.expect("we successfully created a link to the inode, so it must exist"))
    }

    fn remove_hard_link(&mut self, parent_inum: InodeNumber, name: &CStr) -> Result<()> {
        let entry_inum = self.yfs.remove_hard_link(parent_inum, name)?;

        // we update the attributes to reflect the new `nlink`
        let attr = Self::inode_to_attr(&self.yfs, entry_inum)?;
        ensure!(attr.is_none(), "we just removed the entry");
        self.attributes[entry_inum as usize] = attr;

        Ok(())
    }

    /// Converts an inode to a fuse FileAttr.
    ///
    /// Sets uid and gid to 0. Sets permissions to 755.
    fn inode_to_attr(yfs: &Yfs<S>, inum: InodeNumber) -> Result<Option<FileAttr>> {
        let inode = yfs.read_inode(inum)?;

        if inode.type_ == InodeType::Free {
            return Ok(None);
        }

        let time_metadata = yfs.storage.time_metadata().unwrap_or_default();
        let ownership_metadata = yfs.storage.ownership_metadata().unwrap_or_default();

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
        if let Some(attr) = self.get_attributes(ino as InodeNumber) {
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
        if let Ok(attr) = self.set_attributes(ino as InodeNumber, size, atime, mtime, ctime) {
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
                    InodeType::Regular => FileType::RegularFile,
                    InodeType::Directory => FileType::Directory,
                    InodeType::Free => {
                        unreachable!("we filtered these in `self.read_directory`")
                    }
                    InodeType::Symlink => unimplemented!("symlink support is unimplemented"),
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
}
