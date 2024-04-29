use std::mem::size_of;

use serde::{Deserialize, Serialize};
use serde_repr::{Deserialize_repr, Serialize_repr};

use crate::yfs::InodeNumber;

use super::{block::BLOCK_SIZE, boot_sector::BOOT_SECTOR_SIZE, header::FS_HEADER_SIZE};

pub const INODE_SIZE: usize = 64;
const_assert!(size_of::<Inode>() == INODE_SIZE);

pub const NUM_DIRECT: usize = 12;

const_assert!(BLOCK_SIZE % 4 == 0);
pub const NUM_INDIRECT: usize = BLOCK_SIZE / 4;

pub const INODE_START_POSITION: usize = BOOT_SECTOR_SIZE + FS_HEADER_SIZE;

const_assert!(BLOCK_SIZE % INODE_SIZE == 0);
pub const INODES_PER_BLOCK: usize = BLOCK_SIZE / INODE_SIZE;

pub const MAX_FILE_SIZE: usize = (NUM_DIRECT + NUM_INDIRECT) * BLOCK_SIZE;

pub const ROOT_INODE: InodeNumber = 1;

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
