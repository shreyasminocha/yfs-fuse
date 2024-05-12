use std::fs::File;
use std::os::linux::fs::MetadataExt;
use std::os::unix::prelude::FileExt;

use anyhow::{ensure, Context, Result};

use crate::disk_format::block::{Block, BlockNumber, BLOCK_SIZE};
use crate::fs::{OwnershipMetadata, TimeMetadata};

use super::yfs_storage::YfsStorage;

/// YFS storage backed by a file on the host operating system.
pub struct FileBackedStorage(File);

impl FileBackedStorage {
    /// Constructs a new [`FileBackedStorage`] instance.
    #[must_use]
    pub fn new(file: File) -> Self {
        FileBackedStorage(file)
    }
}

impl YfsStorage for FileBackedStorage {
    fn read_block(&self, block_number: BlockNumber) -> Result<Block> {
        ensure!(block_number >= 0, "invalid block number: {block_number}");

        let mut buf = [0; BLOCK_SIZE];
        let position = u64::try_from(block_number)? * u64::try_from(BLOCK_SIZE)?;

        self.0
            .read_at(&mut buf, position)
            .context("reading requested block")?;

        Ok(buf)
    }

    fn write_block(&self, block_number: BlockNumber, block: &Block) -> Result<()> {
        ensure!(block_number >= 0, "invalid block number: {block_number}");

        let position = u64::try_from(block_number)? * u64::try_from(BLOCK_SIZE)?;

        // todo: deal with short writes
        self.0.write_at(block, position).context("writing block")?;

        Ok(())
    }

    fn time_metadata(&self) -> Result<TimeMetadata> {
        let metadata = self.0.metadata()?;

        Ok(TimeMetadata {
            atime: metadata.accessed()?,
            mtime: metadata.modified()?,
            crtime: metadata.created()?,
        })
    }

    fn ownership_metadata(&self) -> Result<OwnershipMetadata> {
        let metadata = self.0.metadata()?;

        Ok(OwnershipMetadata {
            uid: metadata.st_uid(),
            gid: metadata.st_gid(),
        })
    }
}
