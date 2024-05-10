use std::mem::size_of;

use serde::{Deserialize, Serialize};
use serde_repr::{Deserialize_repr, Serialize_repr};

use crate::yfs::InodeNumber;

use super::{block::BLOCK_SIZE, boot_sector::BOOT_SECTOR_SIZE, header::FS_HEADER_SIZE};

/// The number of bytes occupied by an inode.
pub const INODE_SIZE: usize = 64;
const_assert!(size_of::<Inode>() == INODE_SIZE);

/// The number of direct block numbers supported by an inode.
pub const NUM_DIRECT: usize = 12;

const_assert!(BLOCK_SIZE % 4 == 0);
/// The number of indirect block numbers supported by an inode.
pub const NUM_INDIRECT: usize = BLOCK_SIZE / 4;

/// The position in the disk (in bytes) where the first inode begins.
pub const INODE_START_POSITION: usize = BOOT_SECTOR_SIZE + FS_HEADER_SIZE;

const_assert!(BLOCK_SIZE % INODE_SIZE == 0);
/// The number of inodes that can fit in a block.
pub const INODES_PER_BLOCK: usize = BLOCK_SIZE / INODE_SIZE;

/// The maximum supported file size.
pub const MAX_FILE_SIZE: usize = (NUM_DIRECT + NUM_INDIRECT) * BLOCK_SIZE;

/// The inode number of the root inode.
pub const ROOT_INODE: InodeNumber = 1;

/// A free inode.
pub const FREE_INODE: Inode = Inode {
    type_: InodeType::Free,
    nlink: 0,
    reuse: 0,
    size: 0,
    direct: [0; NUM_DIRECT],
    indirect: 0,
};

/// An inode.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct Inode {
    /// File type (e.g., directory or regular file).
    pub type_: InodeType,
    /// Number of hard links to the inode.
    pub nlink: i16,
    /// Number of times the inode has been reused since the filesystem was formatted.
    pub reuse: i32,
    /// File size in bytes.
    pub size: i32,
    /// The block numbers associated with the first [`NUM_DIRECT`] blocks.
    pub direct: [i32; NUM_DIRECT],
    /// The block number of the indirect block (or zero, if none).
    pub indirect: i32,
}

impl Inode {
    /// Constructs a new [`Inode`] instance with reasonable defaults.
    pub fn new(type_: InodeType, reuse: i32) -> Self {
        Inode {
            type_,
            nlink: match type_ {
                InodeType::Free => 0,
                InodeType::Directory => 2,
                InodeType::Regular | InodeType::Symlink => 1,
            },
            reuse,
            size: 0,
            direct: [0; NUM_DIRECT],
            indirect: 0,
        }
    }
}

/// The type of an inode.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize_repr, Deserialize_repr)]
#[repr(i16)]
pub enum InodeType {
    /// Not in use for any file.
    Free = 0,
    /// A directory.
    Directory = 1,
    /// A regular data file.
    Regular = 2,
    /// A symbolic link.
    Symlink = 3,
}
