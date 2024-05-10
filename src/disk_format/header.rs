use std::mem::size_of;

use serde::{Deserialize, Serialize};

use super::inode::INODE_SIZE;

/// The number of bytes occupied by the filesystem header.
pub const FS_HEADER_SIZE: usize = INODE_SIZE;
const_assert!(size_of::<FileSystemHeader>() == FS_HEADER_SIZE);

/// The block number that includes the filesystem header. The header occupies the first
/// [`FS_HEADER_SIZE`] bytes of that block.
pub const FS_HEADER_BLOCK_NUMBER: usize = 1;

/// The filesystem header.
#[derive(Serialize, Deserialize)]
#[repr(C)]
pub struct FileSystemHeader {
    /// The number of blocks in the underlying disk.
    pub num_blocks: i32,
    /// The number of inodes in the underlying disk.
    pub num_inodes: i32,
    /// Padding to make the struct occupy exactly as many bytes as [`INODE_SIZE`].
    pub padding: [i32; 14],
}
