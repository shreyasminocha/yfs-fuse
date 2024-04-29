use std::mem::size_of;

/// size of a disk sector in bytes
const SECTOR_SIZE: usize = 512;

/// size of a block in bytes
pub const BLOCK_SIZE: usize = SECTOR_SIZE;

pub type Block = [u8; BLOCK_SIZE];
const_assert!(size_of::<Block>() == BLOCK_SIZE);
