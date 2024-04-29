use anyhow::Result;

use crate::disk_format::block::Block;
use crate::metadata::{OwnershipMetadata, TimeMetadata};
use crate::yfs::BlockNumber;

pub trait YfsStorage {
    fn read_block(&self, block_number: BlockNumber) -> Result<Block>;

    fn write_block(&self, block_number: BlockNumber, block: Block) -> Result<()>;

    fn time_metadata(&self) -> Result<TimeMetadata> {
        Ok(TimeMetadata::default())
    }

    fn ownership_metadata(&self) -> Result<OwnershipMetadata> {
        Ok(OwnershipMetadata::default())
    }
}
