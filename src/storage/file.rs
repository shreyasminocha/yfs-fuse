use std::fs::File;
use std::os::linux::fs::MetadataExt;
use std::os::unix::prelude::FileExt;

use anyhow::{Context, Result};

use crate::disk_format::block::{Block, BLOCK_SIZE};
use crate::metadata::{OwnershipMetadata, TimeMetadata};
use crate::yfs::BlockNumber;

use super::yfs_storage::YfsStorage;

pub struct FileBackedStorage(File);

impl FileBackedStorage {
    pub fn new(file: File) -> Self {
        FileBackedStorage(file)
    }
}

impl YfsStorage for FileBackedStorage {
    fn read_block(&self, block_number: BlockNumber) -> Result<Block> {
        let mut buf = [0; BLOCK_SIZE];
        let position = block_number * BLOCK_SIZE;

        self.0
            .read_at(&mut buf, position as u64)
            .context("reading requested block")?;

        Ok(buf)
    }

    fn write_block(&self, block_number: BlockNumber, block: Block) -> Result<()> {
        let position = block_number * BLOCK_SIZE;

        // todo: deal with short writes
        self.0
            .write_at(&block, position as u64)
            .context("writing block")?;

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
