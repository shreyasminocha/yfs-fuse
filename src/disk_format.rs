//! Constants and structures that define the YFS disk format.

use std::{
    ffi::{CStr, CString},
    fmt,
};

use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use serde_repr::{Deserialize_repr, Serialize_repr};

use crate::yfs::InodeNumber;

/// size of a disk sector in bytes
const SECTOR_SIZE: usize = 512;

/// size of a block in bytes
pub const BLOCK_SIZE: usize = SECTOR_SIZE;

pub const BOOT_SECTOR_SIZE: usize = SECTOR_SIZE;

/// number of sectors on the disk
pub const _NUM_SECTORS: usize = 1426;

pub const INODE_SIZE: usize = 64;
pub const NUM_DIRECT: usize = 12;
pub const NUM_INDIRECT: usize = BLOCK_SIZE / 4;

pub const FS_HEADER_BLOCK_NUMBER: usize = 1;
pub const FS_HEADER_SIZE: usize = INODE_SIZE;

pub const INODE_START_POSITION: usize = BOOT_SECTOR_SIZE + FS_HEADER_SIZE;

pub const INODES_PER_BLOCK: usize = BLOCK_SIZE / INODE_SIZE;

pub const ROOT_INODE: InodeNumber = 1;

pub const DIRECTORY_ENTRY_SIZE: usize = 32;

pub const MAX_FILE_SIZE: usize = (NUM_DIRECT + NUM_INDIRECT) * BLOCK_SIZE;

pub type Block = [u8; BLOCK_SIZE];

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct Inode {
    /// file type (e.g., directory or regular)
    pub type_: InodeType,
    /// number of hard links to inode
    pub nlink: i16,
    /// inode reuse count
    pub reuse: i32,
    /// file size in bytes
    pub size: i32,
    /// block #s for 1st NUM_DIRECT blocks
    pub direct: [i32; NUM_DIRECT],
    /// block number of indirect block
    pub indirect: i32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize_repr, Deserialize_repr)]
#[repr(i16)]
pub enum InodeType {
    /// This inode is not in use for any file.
    Free = 0,
    /// This inode describes a directory.
    Directory = 1,
    /// This inode describes a regular data file.
    Regular = 2,
    /// This inode describes a symbolic link.
    Symlink = 3,
}

#[derive(Serialize, Deserialize)]
#[repr(C)]
pub struct FileSystemHeader {
    pub num_blocks: i32,
    pub num_inodes: i32,
    pub padding: [i32; 14],
}

#[derive(Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct DirectoryEntry {
    /// inode number
    pub inum: i16,
    /// file name (not null-terminated)
    pub name: DirectoryName,
}

impl DirectoryEntry {
    pub fn new(inum: i16, name: &CStr) -> Result<DirectoryEntry> {
        Ok(DirectoryEntry {
            inum,
            name: name.try_into()?,
        })
    }
}

#[derive(Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DirectoryName([u8; 30]);

impl TryFrom<&CStr> for DirectoryName {
    type Error = anyhow::Error;

    fn try_from(value: &CStr) -> Result<Self, Self::Error> {
        if value.count_bytes() > 30 {
            bail!("string is more than 30 characters long")
        }

        let bytes = value.to_bytes();
        let mut converted = [0; 30];
        converted[0..bytes.len()].copy_from_slice(bytes);

        Ok(DirectoryName(converted))
    }
}

impl From<&DirectoryName> for CString {
    fn from(val: &DirectoryName) -> Self {
        let mut bytes = val.0.to_vec();
        bytes.push(0); // add a nul byte in case there are none

        CString::from(CStr::from_bytes_until_nul(&bytes).expect("we suffixed a nul byte"))
    }
}

impl fmt::Display for DirectoryName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let cstr = CString::from(self);
        let Ok(string) = cstr.into_string() else {
            return Err(fmt::Error);
        };

        write!(f, "{string}")
    }
}
