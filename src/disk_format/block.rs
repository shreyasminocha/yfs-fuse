use std::mem::size_of;

/// Size of a disk sector in bytes.
const SECTOR_SIZE: usize = 512;

/// Size of a block in bytes.
pub const BLOCK_SIZE: usize = SECTOR_SIZE;

/// A YFS block.
pub type Block = [u8; BLOCK_SIZE];
const_assert!(size_of::<Block>() == BLOCK_SIZE);
