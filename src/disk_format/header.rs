use std::mem::size_of;

use serde::{Deserialize, Serialize};

use super::inode::INODE_SIZE;

pub const FS_HEADER_SIZE: usize = INODE_SIZE;
const_assert!(size_of::<FileSystemHeader>() == FS_HEADER_SIZE);

pub const FS_HEADER_BLOCK_NUMBER: usize = 1;

#[derive(Serialize, Deserialize)]
#[repr(C)]
pub struct FileSystemHeader {
    pub num_blocks: i32,
    pub num_inodes: i32,
    pub padding: [i32; 14],
}
