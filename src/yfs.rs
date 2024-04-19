use std::os::linux::fs::MetadataExt;
use std::{fs::File, os::unix::prelude::FileExt};

use anyhow::{bail, Context, Result};
use bitvec::vec::BitVec;

use crate::disk_format::{
    DirectoryEntry, FileSystemHeader, Inode, BLOCK_SIZE, BOOT_SECTOR_SIZE, FS_HEADER_BLOCK_NUMBER,
    INODE_SIZE, NUM_DIRECT, NUM_INDIRECT,
};
use crate::fs::{OwnershipMetadata, TimeMetadata};

// inode numbers are represented as `i16`s on the disk, but we use `u16`s for logical accuracy
pub type InodeNumber = u16;

type Block = [u8; BLOCK_SIZE];

pub struct YfsDisk {
    pub file: File,
    pub num_blocks: usize,
    pub num_inodes: usize,
    pub block_bitmap: BitVec,
}

impl YfsDisk {
    pub fn from_file(file: File) -> Result<Self> {
        let mut header = [0; BLOCK_SIZE];
        let position = FS_HEADER_BLOCK_NUMBER * BLOCK_SIZE;

        file.read_at(&mut header, position as u64)
            .context("unable to read disk header")?;

        let header: FileSystemHeader =
            bincode::deserialize(&header).context("unable to parse disk header")?;

        let num_blocks = header.num_blocks as usize;
        let num_inodes = header.num_inodes as usize;

        let mut block_bitmap = BitVec::new();
        block_bitmap.resize(num_blocks, false);

        // the first block is the header block
        // the next few blocks are blocks full of inodes
        let last_inode_block = 1 + num_inodes.div_ceil(BLOCK_SIZE / INODE_SIZE);
        for b in 0..=last_inode_block {
            block_bitmap.set(b, true);
        }

        Ok(Self {
            file,
            num_blocks,
            num_inodes,
            block_bitmap,
        })
    }

    pub fn read_inode(&self, inum: InodeNumber) -> Result<Inode> {
        if inum == 0 {
            bail!("invalid inode number");
        }

        let position = BOOT_SECTOR_SIZE + (inum as usize * INODE_SIZE);
        let block_number = position / BLOCK_SIZE;
        let offset = position % BLOCK_SIZE;

        let block = self.get_block(block_number)?;
        let inode = &block[offset..offset + INODE_SIZE];

        bincode::deserialize(inode).context("unable to parse inode")
    }

    pub fn read_directory(&self, inode: Inode) -> Result<Vec<DirectoryEntry>> {
        let contents = self.read_file(inode, 0, inode.size as usize)?;

        let mut cursor = &contents[..];
        let mut entries = vec![];
        while let Ok(entry) = bincode::deserialize_from(&mut cursor) {
            entries.push(entry);
        }

        Ok(entries)
    }

    pub fn read_file(&self, inode: Inode, offset: usize, size: usize) -> Result<Vec<u8>> {
        let end = offset + size;

        let mut data = vec![];
        let mut position = offset;
        while position < end {
            let start_offset = position % BLOCK_SIZE;
            let end_position = (position - start_offset + BLOCK_SIZE).min(end);

            let block_index = position / BLOCK_SIZE;
            let block = self.get_file_block(inode, block_index)?;

            data.extend_from_slice(&block[start_offset..end_position - position]);

            position = end_position;
        }

        Ok(data)
    }

    pub fn write_file(&mut self, inode: Inode, offset: usize, data: &[u8]) -> Result<()> {
        let mut position = offset;
        let end = offset + data.len();

        while position < end {
            let start_offset = position % BLOCK_SIZE;
            let end_position = (position - start_offset + BLOCK_SIZE).min(end);

            let block_index = position / BLOCK_SIZE;
            let mut block = self.get_file_block(inode, block_index)?;

            assert_eq!(
                (end_position - position) - start_offset,
                end_position - position
            );

            block[start_offset..end_position - position]
                .copy_from_slice(&data[position..end_position]);

            self.write_file_block(inode, block_index, block)?;

            position = end_position;
        }

        Ok(())
    }

    pub fn time_metadata(&self) -> Result<TimeMetadata> {
        let metadata = self.file.metadata()?;

        Ok(TimeMetadata {
            atime: metadata.accessed()?,
            mtime: metadata.modified()?,
            crtime: metadata.created()?,
        })
    }

    pub fn ownership_metadata(&self) -> Result<OwnershipMetadata> {
        let metadata = self.file.metadata()?;

        Ok(OwnershipMetadata {
            uid: metadata.st_uid(),
            gid: metadata.st_gid(),
        })
    }

    /// Gets the contents of the request block number of the inode.
    ///
    /// Returns a zeroed block if the block number is out of range.
    fn get_file_block(&self, inode: Inode, n: usize) -> Result<Block> {
        let block_number = self.get_file_block_number(inode, n);

        match block_number {
            Ok(b) => self.get_block(b),
            Err(_) => Ok([0; BLOCK_SIZE]),
        }
    }

    fn write_file_block(&self, inode: Inode, n: usize, block: Block) -> Result<()> {
        let block_number = self.get_file_block_number(inode, n)?;
        let position = block_number * BLOCK_SIZE;

        // todo: deal with short writes
        self.file
            .write_at(&block, position as u64)
            .context("writing file block")?;

        Ok(())
    }

    fn get_file_block_number(&self, inode: Inode, n: usize) -> Result<usize> {
        if n < NUM_DIRECT {
            return Ok(inode.direct[n] as usize);
        }

        if n > NUM_DIRECT + NUM_INDIRECT {
            bail!("block index exceeds maximum block count");
        }

        let indirect_block_number: usize = inode
            .indirect
            .try_into()
            .context("converting block number to usize")?;

        let indirect_blocks = self
            .get_block(indirect_block_number)?
            .array_windows::<4>()
            .map(|b| u32::from_le_bytes(*b))
            .collect::<Vec<u32>>();

        Ok(indirect_blocks[n - NUM_DIRECT] as usize)
    }

    fn get_block(&self, block_number: usize) -> Result<Block> {
        let mut buf = [0; BLOCK_SIZE];
        let position = block_number * BLOCK_SIZE;

        self.file
            .read_at(&mut buf, position as u64)
            .context("reading requested block")?;

        Ok(buf)
    }
}
