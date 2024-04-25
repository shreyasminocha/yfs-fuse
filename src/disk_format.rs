//! Constants and structures that define the YFS disk format.

use std::fmt;

use serde::{Deserialize, Serialize};
use serde_repr::{Deserialize_repr, Serialize_repr};

const SECTOR_SIZE: usize = 512;

/// size of a disk sector in bytes
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

pub type Block = [u8; BLOCK_SIZE];

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
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

#[derive(Deserialize)]
#[repr(C)]
pub struct FileSystemHeader {
    pub num_blocks: i32,
    pub num_inodes: i32,
    pub padding: [u8; 14],
}

#[derive(Debug, Deserialize)]
#[repr(C)]
pub struct DirectoryEntry {
    /// inode number
    pub inum: i16,
    /// file name (not null-terminated)
    pub name: DirectoryName,
}

#[derive(Debug, Deserialize)]
pub struct DirectoryName([u8; 30]);

impl fmt::Display for DirectoryName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0
            .into_iter()
            .take_while(|c| *c != 0)
            .try_for_each(|c| write!(f, "{}", c as char))
    }
}
