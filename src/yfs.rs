use std::collections::{HashMap, HashSet};
use std::ffi::{CStr, CString};

use anyhow::{anyhow, bail, Context, Result};
use bitvec::vec::BitVec;
use log::{info, warn};

use crate::disk_format::{
    Block, DirectoryEntry, DirectoryName, FileSystemHeader, Inode, InodeType, BLOCK_SIZE,
    DIRECTORY_ENTRY_SIZE, FS_HEADER_BLOCK_NUMBER, INODES_PER_BLOCK, INODE_SIZE,
    INODE_START_POSITION, MAX_FILE_SIZE, NUM_DIRECT, NUM_INDIRECT, ROOT_INODE,
};
use crate::storage::YfsStorage;

// inode numbers are represented as `i16`s on the disk, but we use `u16`s for logical accuracy
pub type InodeNumber = u16;

// block numbers are represented as `132`s on the disk, but we use `usize`s to avoid littering
// the code with casts.
pub type BlockNumber = usize;

pub struct Yfs<S: YfsStorage> {
    pub storage: S,
    pub num_blocks: usize,
    pub num_inodes: usize,
    pub block_bitmap: BitVec,
}

impl<S: YfsStorage> Yfs<S> {
    pub fn new(storage: S) -> Result<Self> {
        let mut yfs = Self {
            storage,
            num_blocks: FS_HEADER_BLOCK_NUMBER,
            num_inodes: 0,
            block_bitmap: BitVec::new(),
        };

        let header_block = yfs.storage.read_block(FS_HEADER_BLOCK_NUMBER)?;

        let header: FileSystemHeader =
            bincode::deserialize(&header_block).context("unable to parse disk header")?;

        if header.num_blocks < 2 {
            // we need at least the boot sector and the fs header
            bail!("invalid number of blocks: {}", header.num_blocks);
        }

        if header.num_inodes < 1 {
            // we need at least the root inode
            bail!("invalid number of inodes: {}", header.num_inodes);
        }

        if header.num_blocks < (header.num_inodes + 1).div_ceil(INODES_PER_BLOCK as i32) {
            bail!("not enough blocks to store inodes");
        }

        yfs.num_blocks = header.num_blocks as usize;
        yfs.num_inodes = header.num_inodes as usize;

        info!("{} total blocks", yfs.num_blocks);
        info!("{} total inodes", yfs.num_inodes);

        // check that the first and last blocks are accessible
        let _ = yfs.storage.read_block(0)?;
        let _ = yfs.storage.read_block(yfs.num_blocks - 1)?;

        yfs.block_bitmap.resize(yfs.num_blocks, false);

        // sector/block zero is the boot sector.
        yfs.block_bitmap.set(0, true);

        // the first INODE_SIZE bytes of the first inode block are occupied by the
        // file system header
        let last_inode_block = (yfs.num_inodes + 1).div_ceil(INODES_PER_BLOCK);
        for b in 1..=last_inode_block {
            yfs.block_bitmap.set(b, true);
        }

        for inum in 1..=yfs.num_inodes {
            let inode = yfs.read_inode(inum as u16)?;

            if inode.type_ == InodeType::Free {
                if !yfs.get_inode_allocated_block_numbers(inode)?.is_empty() {
                    warn!("free inode has allocated blocks");
                }

                continue;
            }

            let block_numbers = yfs.get_inode_allocated_block_numbers(inode)?;
            for block_number in block_numbers {
                if block_number >= yfs.num_blocks {
                    bail!("invalid block number: {block_number}");
                }

                if block_number <= last_inode_block {
                    bail!("block is used by inodes");
                }

                if yfs.block_bitmap[block_number] {
                    bail!("block number {block_number} is already allocated");
                }

                yfs.block_bitmap.set(block_number, true);
            }

            if inode.indirect != 0 {
                let indirect_block_number = inode.indirect as BlockNumber;

                if inode.indirect < 0 || indirect_block_number >= yfs.num_blocks {
                    bail!("invalid block number: {}", inode.indirect);
                }

                if indirect_block_number <= last_inode_block {
                    bail!("block number {} is used by inodes", indirect_block_number);
                }

                if yfs.block_bitmap[indirect_block_number] {
                    bail!(
                        "block number {} is already allocated",
                        indirect_block_number
                    );
                }

                yfs.block_bitmap.set(indirect_block_number, true);
            }
        }

        // check filesystem for consistency
        yfs.check_filesystem()?;

        Ok(yfs)
    }

    pub fn read_directory(&self, inum: InodeNumber) -> Result<Vec<DirectoryEntry>> {
        let inode = self.read_inode(inum)?;
        let contents = self.read_file(inum, 0, inode.size as usize)?;

        let mut entries = vec![];

        for chunk in contents.chunks_exact(DIRECTORY_ENTRY_SIZE) {
            let entry: DirectoryEntry = bincode::deserialize(chunk)?;

            if entry.inum == 0 {
                // "free directory entry"
                if entry.name != DirectoryName::default() {
                    warn!("free directory entry has non-empty name");
                }

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
            bail!("invalid inode number: {inum}");
        }

        let position = INODE_START_POSITION + ((inum - 1) as usize * INODE_SIZE);
        let block_number = position / BLOCK_SIZE;
        let offset = position % BLOCK_SIZE;

        let block = self.storage.read_block(block_number)?;
        let inode = &block[offset..offset + INODE_SIZE];

        bincode::deserialize(inode).context("parsing inode")
    }

    pub fn write_inode(&self, inum: InodeNumber, inode: Inode) -> Result<()> {
        if inum == 0 {
            bail!("invalid inode number: {inum}");
        }

        let inode_serialized = bincode::serialize(&inode).context("serializing inode")?;

        let position = INODE_START_POSITION + ((inum - 1) as usize * INODE_SIZE);
        let block_number = position / BLOCK_SIZE;
        let offset = position % BLOCK_SIZE;

        let mut block = self.storage.read_block(block_number)?;
        block[offset..offset + INODE_SIZE].copy_from_slice(&inode_serialized);

        self.storage.write_block(block_number, block)?;

        Ok(())
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
                    let indirect_block_number = self
                        .assign_free_block()
                        .ok_or(anyhow!("no more free blocks"))?;

                    self.storage
                        .write_block(indirect_block_number, [0; BLOCK_SIZE])?;

                    inode.indirect = indirect_block_number as i32;

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
            self.storage
                .write_block(inode.indirect as BlockNumber, indirect_block)?;
        }

        // update the inode with the new direct/indirect blocks
        self.write_inode(inum, inode)?;

        Ok(())
    }

    /// Reads the contents of the request block number of the inode.
    fn read_file_block(&self, inode: Inode, n: usize) -> Result<Block> {
        let block_number = self.get_file_block_number(inode, n)?;
        self.storage.read_block(block_number)
    }

    fn write_file_block(&self, inode: Inode, n: usize, block: Block) -> Result<()> {
        let block_number = self.get_file_block_number(inode, n)?;
        self.storage.write_block(block_number, block)
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
            .storage
            .read_block(indirect_block_number)?
            .array_chunks::<4>()
            .map(|b| u32::from_le_bytes(*b) as BlockNumber)
            .collect::<Vec<_>>()
            .try_into()
            .expect("NUM_DIRECT is defined as BLOCK_SIZE divided by 4");

        Ok(Some(indirect_blocks))
    }

    fn assign_free_block(&mut self) -> Option<BlockNumber> {
        let assigned = self.block_bitmap.first_zero();

        if let Some(block) = assigned {
            self.block_bitmap.set(block, true);
        }

        assigned
    }

    /// Checks the filesystem for consistency. Performs a depth-first traversal of the directory
    /// tree.
    ///
    /// Does not check for the validity of allocated blocks or block reuse. Some checks are
    /// exclusively performed in [`Self::new`].
    fn check_filesystem(&self) -> Result<()> {
        let root_inode = self.read_inode(ROOT_INODE)?;
        if root_inode.type_ != InodeType::Directory {
            bail!("root inode does not represent a directory");
        }

        let mut queue = vec![ROOT_INODE];
        let mut seen_directories = HashSet::<InodeNumber>::new();
        let mut directory_parents = HashMap::from([(ROOT_INODE, ROOT_INODE)]);

        const DOT: &CStr = c".";
        const DOT_DOT: &CStr = c"..";

        while let Some(inum) = queue.pop() {
            let inode = self.read_inode(inum)?;
            if inode.type_ == InodeType::Free {
                bail!("directory tree includes free inode");
            }

            if inode.size < 0 {
                bail!("invalid size in inode: {}", inode.size);
            }

            if inode.size as usize > MAX_FILE_SIZE {
                bail!("size in inode is greater than the maximum valid file size");
            }

            if self.get_inode_allocated_block_numbers(inode)?.len()
                < (inode.size as usize).div_ceil(BLOCK_SIZE)
            {
                bail!(
                    "inode doesn't have enough blocks to store {} bytes",
                    inode.size
                );
            }

            if inode.type_ == InodeType::Directory {
                if seen_directories.contains(&inum) {
                    bail!("directory tree includes loop");
                }

                seen_directories.insert(inum);

                let parent_inum = *directory_parents
                    .get(&inum)
                    .expect("this directory was discovered through the entries of some directory");

                if inode.size as usize % DIRECTORY_ENTRY_SIZE != 0 {
                    bail!(
                        "directory size {} is not a multiple of the directory entry size",
                        inode.size
                    );
                }

                let mut entry_names: HashSet<CString> = HashSet::new();

                for entry in self.read_directory(inum)? {
                    if entry.inum < 0 || entry.inum as usize > self.num_inodes {
                        bail!("invalid inode number in directory entry: {}", entry.inum);
                    }

                    let entry_inum = entry.inum as InodeNumber;
                    let entry_name = CString::from(&entry.name);
                    let entry_name = entry_name.as_c_str();

                    if entry_names.contains(entry_name) {
                        bail!("directory contains duplicate entry: {}", entry.name);
                    }
                    entry_names.insert(entry_name.to_owned());

                    if entry_name == DOT && entry_inum != inum {
                        bail!("'.' entry doesn't point to self");
                    }

                    if entry_name == DOT_DOT && entry_inum != parent_inum {
                        bail!("'..' entry doesn't point to parent");
                    }

                    if entry_name == DOT || entry_name == DOT_DOT {
                        // prevent these from interfering with operations for "regular" entries
                        continue;
                    }

                    if entry_name == c"" {
                        bail!("invalid directory entry name: \"\"");
                    }

                    let entry_inode = self.read_inode(entry_inum)?;
                    if entry_inode.type_ == InodeType::Directory {
                        directory_parents.insert(entry_inum, inum);
                    }

                    queue.push(entry.inum as InodeNumber);
                }

                if !entry_names.contains(DOT) {
                    bail!("no '.' entry");
                }

                if !entry_names.contains(DOT_DOT) {
                    bail!("no '..' entry");
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    mod validation {
        #[test]
        fn test_invalid_num_inodes() {}

        #[test]
        fn test_negative_num_blocks() {}

        #[test]
        fn test_invalid_direct_block_block() {}

        #[test]
        fn test_invalid_indirect_block_block() {}

        #[test]
        fn test_direct_block_pointing_to_inodes() {}

        #[test]
        fn test_indirect_block_pointing_to_inodes() {}

        #[test]
        fn test_doubly_allocated_block() {}

        #[test]
        fn test_inode_without_enough_blocks() {}

        #[test]
        fn test_inode_with_too_many_blocks() {}

        #[test]
        fn test_inode_with_negative_size() {}

        #[test]
        fn test_inode_with_size_exceeding_the_maximum() {}

        #[test]
        fn test_no_root_inode() {}

        #[test]
        fn test_non_directory_root_inode() {}

        #[test]
        fn test_directory_invalid_size() {}

        #[test]
        fn test_directory_invalid_entry_inum() {}

        #[test]
        fn test_directory_free_entry() {}

        #[test]
        fn test_directory_duplicate_entries() {}

        #[test]
        fn test_directory_no_dot() {}

        #[test]
        fn test_directory_invalid_dot() {}

        #[test]
        fn test_directory_no_dot_dot() {}

        #[test]
        fn test_directory_invalid_dot_dot() {}

        #[test]
        fn test_directory_loop() {}
    }
}
