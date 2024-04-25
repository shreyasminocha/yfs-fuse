use std::os::linux::fs::MetadataExt;
use std::{fs::File, os::unix::prelude::FileExt};

use anyhow::{anyhow, bail, Context, Result};
use bitvec::vec::BitVec;
use log::{info, warn};

use crate::disk_format::{
    DirectoryEntry, FileSystemHeader, Inode, InodeType, BLOCK_SIZE, FS_HEADER_BLOCK_NUMBER,
    INODE_SIZE, INODE_START_POSITION, NUM_DIRECT, NUM_INDIRECT,
};
use crate::fs::{OwnershipMetadata, TimeMetadata};

// inode numbers are represented as `i16`s on the disk, but we use `u16`s for logical accuracy
pub type InodeNumber = u16;

// block numbers are represented as `132`s on the disk, but we use `usize`s to avoid littering
// the code with casts.
type BlockNumber = usize;

type Block = [u8; BLOCK_SIZE];

pub struct Yfs {
    pub file: File,
    pub num_blocks: usize,
    pub num_inodes: usize,
    pub block_bitmap: BitVec,
}

impl Yfs {
    pub fn from_file(file: File) -> Result<Self> {
        let mut yfs = Self {
            file,
            num_blocks: FS_HEADER_BLOCK_NUMBER,
            num_inodes: 0,
            block_bitmap: BitVec::new(),
        };

        let header_block = yfs.read_block(FS_HEADER_BLOCK_NUMBER)?;

        let header: FileSystemHeader =
            bincode::deserialize(&header_block).context("unable to parse disk header")?;

        yfs.num_blocks = header.num_blocks as usize;
        yfs.num_inodes = header.num_inodes as usize;

        info!("{} total blocks", yfs.num_blocks);
        info!("{} total inodes", yfs.num_inodes);

        yfs.block_bitmap.resize(yfs.num_blocks, false);

        // block numbers are one-indexed. sector zero is the boot sector.
        yfs.block_bitmap.set(0, true);

        // the first block is the header block
        // the next few blocks are blocks full of inodes
        let last_inode_block = 1 + yfs.num_inodes.div_ceil(BLOCK_SIZE / INODE_SIZE);
        for b in 1..=last_inode_block {
            yfs.block_bitmap.set(b, true);
        }

        for inum in 1..=yfs.num_inodes {
            let inode = yfs.read_inode(inum as u16)?;
            if inode.type_ == InodeType::Free {
                continue;
            }

            let block_numbers = yfs.get_inode_allocated_block_numbers(inode)?;
            for block_number in block_numbers {
                yfs.block_bitmap.set(block_number, true);
            }

            if inode.indirect != 0 {
                yfs.block_bitmap.set(inode.indirect as BlockNumber, true);
            }
        }

        Ok(yfs)
    }

    pub fn read_directory(&self, inum: InodeNumber) -> Result<Vec<DirectoryEntry>> {
        let inode = self.read_inode(inum)?;
        let contents = self.read_file(inum, 0, inode.size as usize)?;

        let mut cursor = &contents[..];
        let mut entries = vec![];
        while let Ok(entry) = bincode::deserialize_from::<_, DirectoryEntry>(&mut cursor) {
            if entry.inum == 0 {
                // "free directory entry"
                continue;
            }

            entries.push(entry);
        }

        Ok(entries)
    }

    pub fn read_file(&self, inum: InodeNumber, offset: usize, size: usize) -> Result<Vec<u8>> {
        info!("[inode #{inum}] reading file (offset = {offset}; size = {size})");

        let inode = self.read_inode(inum)?;

        let end = (offset + size).min(inode.size as usize);

        let mut data = vec![];
        let mut position = offset;
        while position < end {
            let start_offset = position % BLOCK_SIZE;
            let block_start = position - start_offset;
            let block_end = block_start + BLOCK_SIZE;
            let end_position = block_end.min(end);

            let block_index = position / BLOCK_SIZE;
            let Ok(block) = self.read_file_block(inode, block_index) else {
                // the requested read size can sometimes be bigger than the file size
                // in such a case, we want to fail gracefully
                break;
            };

            data.extend_from_slice(&block[start_offset..end_position - block_start]);

            position = end_position;
        }

        Ok(data)
    }

    pub fn write_file(&mut self, inum: InodeNumber, offset: usize, data: &[u8]) -> Result<usize> {
        info!(
            "[inode #{inum}] writing file (offset = {offset}; data.len() = {})",
            data.len()
        );

        let mut position = offset;
        let end = offset + data.len();

        self.grow_file(inum, end)?; // grows file only if necessary

        // we're careful to read the inode *after* potentially growing the file
        // because that operation manipulates the inode
        let mut inode = self.read_inode(inum)?;

        let mut write_len = 0;
        while position < end {
            let start_offset = position % BLOCK_SIZE;
            let block_start = position - start_offset;
            let block_end = block_start + BLOCK_SIZE;
            let end_position = block_end.min(end);

            let block_index = position / BLOCK_SIZE;
            let mut block = self.read_file_block(inode, block_index)?;

            block[start_offset..end_position - block_start]
                .copy_from_slice(&data[(position - offset)..(end_position - offset)]);

            self.write_file_block(inode, block_index, block)?;

            write_len += end_position - position;
            position = end_position;
        }

        inode.size = inode.size.max((offset + write_len) as i32);
        self.write_inode(inum, inode)?;

        info!("[inode #{inum}] wrote {write_len} bytes");
        Ok(write_len)
    }

    pub fn read_inode(&self, inum: InodeNumber) -> Result<Inode> {
        if inum == 0 {
            bail!("invalid inode number");
        }

        let position = INODE_START_POSITION + ((inum - 1) as usize * INODE_SIZE);
        let block_number = position / BLOCK_SIZE;
        let offset = position % BLOCK_SIZE;

        let block = self.read_block(block_number)?;
        let inode = &block[offset..offset + INODE_SIZE];

        bincode::deserialize(inode).context("parsing inode")
    }

    pub fn write_inode(&self, inum: InodeNumber, inode: Inode) -> Result<()> {
        if inum == 0 {
            bail!("invalid inode number");
        }

        let inode_serialized = bincode::serialize(&inode).context("serializing inode")?;

        let position = INODE_START_POSITION + ((inum - 1) as usize * INODE_SIZE);
        let block_number = position / BLOCK_SIZE;
        let offset = position % BLOCK_SIZE;

        let mut block = self.read_block(block_number)?;
        block[offset..offset + INODE_SIZE].copy_from_slice(&inode_serialized);

        self.write_block(block_number, block)?;

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

    /// Allocates new blocks if necessary.
    /// Does not update the size stored in the inode.
    fn grow_file(&mut self, inum: InodeNumber, new_size: usize) -> Result<()> {
        let mut inode = self.read_inode(inum)?;

        if new_size <= inode.size as usize {
            // no need to grow the file
            return Ok(());
        }

        let new_num_blocks = new_size.div_ceil(BLOCK_SIZE);

        let mut i = 0;
        for block_number in inode.direct.iter_mut() {
            if i >= new_num_blocks {
                break;
            }

            if *block_number == 0 {
                *block_number = self
                    .assign_free_block()
                    .ok_or(anyhow!("no more free blocks"))? as i32;
            }

            i += 1;
        }

        // if direct blocks weren't enough, use the indirect block
        if i < new_num_blocks {
            let mut indirect_block_numbers = match self.get_indirect_block_numbers(inode)? {
                Some(block_numbers) => block_numbers,
                None => {
                    inode.indirect =
                        self.assign_free_block()
                            .ok_or(anyhow!("no more free blocks"))? as i32;

                    // todo: maybe ensure that that block is just zeroes

                    [0; NUM_INDIRECT]
                }
            };

            for block_number in indirect_block_numbers.iter_mut() {
                if i >= new_num_blocks {
                    break;
                }

                if *block_number == 0 {
                    *block_number = self
                        .assign_free_block()
                        .ok_or(anyhow!("no more free blocks"))?;
                }

                i += 1;
            }

            // write indirect_block_numbers to the indirect block
            let indirect_block = indirect_block_numbers
                .into_iter()
                .flat_map(|b| u32::to_le_bytes(b as u32))
                .collect::<Vec<_>>()
                .try_into()
                .expect("NUM_INDIRECT = BLOCK_SIZE / 4. So, NUM_INDIRECT * 4 == BLOCK_SIZE");
            self.write_block(inode.indirect as BlockNumber, indirect_block)?;
        }

        // update the inode with the new direct/indirect blocks
        self.write_inode(inum, inode)?;

        Ok(())
    }

    /// Reads the contents of the request block number of the inode.
    fn read_file_block(&self, inode: Inode, n: usize) -> Result<Block> {
        let block_number = self.get_file_block_number(inode, n)?;
        self.read_block(block_number)
    }

    fn write_file_block(&self, inode: Inode, n: usize, block: Block) -> Result<()> {
        let block_number = self.get_file_block_number(inode, n)?;
        self.write_block(block_number, block)
    }

    fn get_file_block_number(&self, inode: Inode, n: usize) -> Result<BlockNumber> {
        if n > NUM_DIRECT + NUM_INDIRECT {
            bail!("block index exceeds maximum block count");
        }

        let block_numbers = self.get_inode_allocated_block_numbers(inode)?;

        Ok(*block_numbers
            .get(n)
            .ok_or(anyhow!("block index exceeds allocated block count"))?)
    }

    fn get_inode_allocated_block_numbers(&self, inode: Inode) -> Result<Vec<BlockNumber>> {
        let direct_blocks = inode
            .direct
            .into_iter()
            .take_while(|b| *b != 0)
            .map(|b| b as usize)
            .collect::<Vec<_>>();

        let indirect_blocks = self
            .get_indirect_block_numbers(inode)?
            .unwrap_or([0; NUM_INDIRECT])
            .into_iter()
            .take_while(|b| *b != 0)
            .collect::<Vec<_>>();

        if direct_blocks.len() != NUM_DIRECT && !indirect_blocks.is_empty() {
            warn!("inode has indirect block even though not all direct blocks are used");
        }

        Ok([direct_blocks, indirect_blocks].concat())
    }

    fn get_indirect_block_numbers(
        &self,
        inode: Inode,
    ) -> Result<Option<[BlockNumber; NUM_INDIRECT]>> {
        let indirect_block_number: BlockNumber = inode
            .indirect
            .try_into()
            .context("converting block number to BlockNumber")?;

        if indirect_block_number == 0 {
            return Ok(None);
        }

        let indirect_blocks = self
            .read_block(indirect_block_number)?
            .array_chunks::<4>()
            .map(|b| u32::from_le_bytes(*b) as BlockNumber)
            .collect::<Vec<_>>()
            .try_into()
            .expect("NUM_DIRECT is defined as BLOCK_SIZE divided by 4");

        Ok(Some(indirect_blocks))
    }

    fn read_block(&self, block_number: BlockNumber) -> Result<Block> {
        let mut buf = [0; BLOCK_SIZE];
        let position = block_number * BLOCK_SIZE;

        self.file
            .read_at(&mut buf, position as u64)
            .context("reading requested block")?;

        Ok(buf)
    }

    fn write_block(&self, block_number: BlockNumber, block: Block) -> Result<()> {
        let position = block_number * BLOCK_SIZE;

        // todo: deal with short writes
        self.file
            .write_at(&block, position as u64)
            .context("writing block")?;

        Ok(())
    }

    fn assign_free_block(&mut self) -> Option<BlockNumber> {
        let assigned = self.block_bitmap.first_zero();

        if let Some(block) = assigned {
            self.block_bitmap.set(block, true);
        }

        assigned
    }
}
