use anyhow::Result;

use crate::disk_format::block::Block;
use crate::metadata::{OwnershipMetadata, TimeMetadata};
use crate::yfs::BlockNumber;

/// An abstraction that allows reading and writing YFS-style blocks.
pub trait YfsStorage {
    /// Reads the block at the given block number.
    fn read_block(&self, block_number: BlockNumber) -> Result<Block>;

    /// Writes to the block at the given block number.
    fn write_block(&self, block_number: BlockNumber, block: Block) -> Result<()>;

    /// Returns time metadata associated with the storage medium.
    fn time_metadata(&self) -> Result<TimeMetadata> {
        Ok(TimeMetadata::default())
    }

    /// Returns ownership metadata associated with the storage medium.
    fn ownership_metadata(&self) -> Result<OwnershipMetadata> {
        Ok(OwnershipMetadata::default())
    }
}
