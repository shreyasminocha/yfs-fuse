use std::ffi::{CStr, CString};
use std::{
    collections::{HashMap, HashSet},
    convert::Into,
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use bitvec::vec::BitVec;
use log::{info, warn};

use crate::{
    disk_format::{
        block::{Block, BlockNumber, BLOCK_SIZE},
        directory_entry::{
            DirectoryEntry, DirectoryEntryName, DIRECTORY_ENTRIES_PER_BLOCK, DIRECTORY_ENTRY_SIZE,
            FREE_DIRECTORY_ENTRY,
        },
        header::{FileSystemHeader, FS_HEADER_BLOCK_NUMBER},
        inode::{
            Inode, InodeNumber, InodeType, FREE_INODE, INODES_PER_BLOCK, INODE_SIZE,
            INODE_START_POSITION, MAX_FILE_SIZE, NUM_DIRECT, NUM_INDIRECT, ROOT_INODE,
        },
    },
    storage::YfsStorage,
};

/// Implements YFS operations independent.
pub struct Yfs<S: YfsStorage> {
    /// The abstraction that allows us to read and write sectors without worrying about where or how
    /// sectors are persisted.
    pub storage: S,
    /// The number of blocks in the disk, including the boot block, the filesystem header, blocks
    /// occupied by the inode, and data blocks.
    pub num_blocks: i32,
    /// The number of inodes in the disk.
    pub num_inodes: i16,
    /// Tracks the allocation status of blocks.
    ///
    /// A value of `true` or "one" represents "occupied" and vice-versa.
    block_bitmap: BitVec,
    /// Tracks the allocation status of inodes.
    ///
    /// A value of `true` or "one" represents "occupied" and vice-versa.
    inode_bitmap: BitVec,
}

impl<S: YfsStorage> Yfs<S> {
    /// Constructs a new instance of [`Yfs`].
    pub fn new(storage: S) -> Result<Self> {
        let mut yfs = Self {
            storage,
            num_blocks: FS_HEADER_BLOCK_NUMBER,
            num_inodes: 0,
            block_bitmap: BitVec::new(),
            inode_bitmap: BitVec::new(),
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

        yfs.num_blocks = header.num_blocks;
        yfs.num_inodes = header
            .num_inodes
            .try_into()
            .context("we should be able to refer to all inodes with i16s")?;

        info!("{} total blocks", yfs.num_blocks);
        info!("{} total inodes", yfs.num_inodes);

        // check that the first and last blocks are accessible
        let _ = yfs.storage.read_block(0)?;
        let _ = yfs.storage.read_block(yfs.num_blocks - 1)?;

        yfs.block_bitmap.resize(yfs.num_blocks.try_into()?, false);
        // inodes are one-indexed. we add one to simplify indexing
        yfs.inode_bitmap
            .resize(usize::try_from(yfs.num_inodes)? + 1, false);

        // sector/block zero is the boot sector.
        yfs.block_bitmap.set(0, true);
        // inode zero doesn't exist
        yfs.inode_bitmap.set(0, true);

        // the first INODE_SIZE bytes of the first inode block are occupied by the
        // file system header
        let last_inode_block = (usize::try_from(yfs.num_inodes)? + 1).div_ceil(INODES_PER_BLOCK);
        for b in 1..=last_inode_block {
            yfs.block_bitmap.set(b, true);
        }

        for inum in 1..=yfs.num_inodes {
            let inode = yfs.read_inode(inum)?;

            if inode.type_ == InodeType::Free {
                if !yfs.get_inode_allocated_block_numbers(inode)?.is_empty() {
                    warn!("free inode has allocated blocks");
                }

                continue;
            }

            // this inode is occupied
            yfs.inode_bitmap.set(inum.try_into()?, true);

            let block_numbers = yfs.get_inode_allocated_block_numbers(inode)?;
            for block_number in block_numbers {
                if block_number >= yfs.num_blocks {
                    bail!("invalid block number: {block_number}");
                }

                let block_number: usize = block_number.try_into()?;

                if block_number <= last_inode_block {
                    bail!("block is used by inodes");
                }

                if yfs.block_bitmap[block_number] {
                    bail!("block number {block_number} is already allocated");
                }

                yfs.block_bitmap.set(block_number, true);
            }

            if inode.indirect != 0 {
                let indirect_block_number: usize = inode.indirect.try_into()?;

                if inode.indirect < 0 || indirect_block_number >= yfs.num_blocks.try_into()? {
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

    /// Searches for an entry by name within a directory and, if found, returns its inode number.
    pub fn lookup_entry(
        &self,
        parent_inum: InodeNumber,
        name: &CStr,
    ) -> Result<Option<InodeNumber>> {
        Ok(self
            .lookup_directory_entry(parent_inum, name)?
            .map(|(_, entry)| entry.inum))
    }

    /// Returns the entries within a directory, excluding "free" entries, i.e. entries with the
    /// inode number zero.
    pub fn read_directory(&self, inum: InodeNumber) -> Result<Vec<DirectoryEntry>> {
        Ok(self
            .read_directory_entries(inum)?
            .into_iter()
            .filter(|entry| entry.inum != 0)
            .collect())
    }

    /// Reads at most `size` bytes of a file starting at `offset`.
    ///
    /// A `size` that is greater than the size of the file is not an error.
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

    /// Writes `data` to a file starting at `offset`. Returns the number of bytes successfully
    /// written.
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

            self.write_file_block(inode, block_index, &block)?;

            write_len += end_position - position;
            position = end_position;
        }

        inode.size = inode.size.max((offset + write_len) as i32);
        self.write_inode(inum, inode)?;

        info!("[inode #{inum}] wrote {write_len} bytes");
        Ok(write_len)
    }

    /// Creates a new regular file within a given parent directory.
    pub fn create_file(&mut self, parent_inum: InodeNumber, name: &CStr) -> Result<InodeNumber> {
        self.create(parent_inum, name, InodeType::Regular)
    }

    /// Creates a new directory within a given parent directory. Sets up the new directory to
    /// include the '.' and '..' entries.
    pub fn create_directory(
        &mut self,
        parent_inum: InodeNumber,
        name: &CStr,
    ) -> Result<InodeNumber> {
        let new_inum = self.create(parent_inum, name, InodeType::Directory)?;

        // we write a block's worth of entries so that garbage in the newly-allocated block
        // isn't interpreted as an entry
        let mut entries = [FREE_DIRECTORY_ENTRY; DIRECTORY_ENTRIES_PER_BLOCK];
        entries[0] = DirectoryEntry::new(new_inum, c".").expect("'.' is a valid name");
        entries[1] = DirectoryEntry::new(parent_inum, c"..").expect("'..' is a valid name");

        let data = bincode::serialize(&entries)?;
        self.write_file(new_inum, 0, &data)?;

        self.update_inode(parent_inum, |parent_inode| parent_inode.nlink += 1)?;

        Ok(new_inum)
    }

    /// Removes a directory from a given parent directory and frees the resources occupied by it.
    /// The directory being removed *must* be empty except for the '.' and '..' entries.
    pub fn remove_directory(
        &mut self,
        parent_inum: InodeNumber,
        name: &CStr,
    ) -> Result<InodeNumber> {
        let (entry_offset, entry) = self
            .lookup_directory_entry(parent_inum, name)?
            .ok_or(anyhow!("entry does not exist: {name:?}"))?;

        let entry_inode = self.read_inode(entry.inum)?;
        ensure!(
            entry_inode.type_ == InodeType::Directory,
            "can rmdir only directories"
        );

        let entry_chlidren = self.read_directory(entry.inum)?;
        let entry_children: Vec<_> = entry_chlidren
            .iter()
            .filter(|child| {
                let name = CString::from(&child.name);
                let name: &CStr = &name;
                name != c"." && name != c".."
            })
            .collect();
        ensure!(
            entry_children.is_empty(),
            "cannot remove non-empty directories"
        );

        ensure!(entry.inum != ROOT_INODE, "cannot rmdir root directory");

        self.remove_entry_at_offset(parent_inum, entry_offset)?;

        // entry's '..' child no longer points to the parent
        self.update_inode(parent_inum, |parent_inode| parent_inode.nlink -= 1)?;

        self.delete_inode(entry.inum)?;

        Ok(entry.inum)
    }

    /// Creates a hard link to a file within a given directory with a given name.
    pub fn create_hard_link(
        &mut self,
        parent_inum: InodeNumber,
        name: &CStr,
        inum: InodeNumber,
    ) -> Result<()> {
        let parent_inode = self.read_inode(parent_inum)?;
        ensure!(
            parent_inode.type_ == InodeType::Directory,
            "parent is not a directory: {parent_inum}"
        );

        let mut inode = self.read_inode(inum)?;
        ensure!(
            [InodeType::Regular, InodeType::Symlink].contains(&inode.type_),
            "can create hard links to regular files and symlinks only"
        );

        let new_entry = DirectoryEntry::new(inum, name)?;
        self.add_directory_entry(parent_inum, &new_entry)?;

        inode.nlink += 1;
        self.write_inode(inum, inode)?;

        Ok(())
    }

    /// Removes a hard link from a directory.
    pub fn remove_hard_link(
        &mut self,
        parent_inum: InodeNumber,
        name: &CStr,
    ) -> Result<InodeNumber> {
        ensure!(
            name != c"." && name != c"..",
            "cannot remove '.' and '..' entries"
        );

        let (entry_offset, entry) = self
            .lookup_directory_entry(parent_inum, name)?
            .ok_or(anyhow!("entry does not exist: {name:?}"))?;

        let mut entry_inode = self.read_inode(entry.inum)?;

        ensure!(
            [InodeType::Regular, InodeType::Symlink].contains(&entry_inode.type_),
            "can unlink only regular files and symlinks"
        );

        self.remove_entry_at_offset(parent_inum, entry_offset)?;

        entry_inode.nlink -= 1;
        self.write_inode(entry.inum, entry_inode)?;

        if entry_inode.nlink == 0 {
            self.delete_inode(entry.inum)?;
        }

        Ok(entry.inum)
    }

    /// Renames and/or moves a file or directory from a source parent-name pair to a target parent-
    /// name pair. If the target already exists, it is replaced by the source.
    pub fn rename(
        &mut self,
        source_parent_inum: InodeNumber,
        source_name: &CStr,
        target_parent_inum: InodeNumber,
        target_name: &CStr,
    ) -> Result<()> {
        ensure!(
            source_name != c"." && source_name != c"..",
            "cannot rename '.' and '..' entries"
        );

        let (source_entry_offset, source_entry) = self
            .lookup_directory_entry(source_parent_inum, source_name)?
            .ok_or(anyhow!("entry does not exist: {source_name:?}"))?;
        let inum = source_entry.inum;

        if let Some((target_entry_offset, existing_target_entry)) =
            self.lookup_directory_entry(target_parent_inum, target_name)?
        {
            let existing_target_inode = self.read_inode(existing_target_entry.inum)?;
            ensure!(
                existing_target_inode.type_ != InodeType::Directory,
                "rename target name cannot refer to a directory"
            );

            self.remove_hard_link(target_parent_inum, target_name)
                .context("unable to remove rename target")?;

            let new_entry = DirectoryEntry {
                inum,
                ..existing_target_entry
            };
            self.add_entry_at_offset(target_parent_inum, target_entry_offset, &new_entry)?;
        } else {
            let new_entry = DirectoryEntry::new(inum, target_name)?;
            self.add_directory_entry(target_parent_inum, &new_entry)?;
        }

        // remove old entry
        self.remove_entry_at_offset(source_parent_inum, source_entry_offset)?;

        Ok(())
    }

    /// Creates a symbolic link to a given (absolute or relative) path. The path is not checked
    /// for validity.
    pub fn create_symbolic_link(
        &mut self,
        parent_inum: InodeNumber,
        name: &CStr,
        link: &CStr,
    ) -> Result<InodeNumber> {
        let new_inum = self.create(parent_inum, name, InodeType::Symlink)?;
        self.write_file(new_inum, 0, link.to_bytes())?;

        Ok(new_inum)
    }

    /// Reads a given symbolic link and returns its contents (the target path) as a byte vector.
    pub fn read_symbolic_link(&mut self, inum: InodeNumber) -> Result<Vec<u8>> {
        let inode = self.read_inode(inum)?;
        ensure!(
            inode.type_ == InodeType::Symlink,
            "can read symlink only from a symlink"
        );

        self.read_file(inum, 0, inode.size as usize)
    }

    /// Returns the number of free disk blocks.
    pub fn num_free_blocks(&self) -> usize {
        self.block_bitmap.count_zeros()
    }

    /// Returns the number of free inodes.
    pub fn num_free_inodes(&self) -> usize {
        self.inode_bitmap.count_zeros()
    }

    /// Reads the inode at a given inode number.
    pub fn read_inode(&self, inum: InodeNumber) -> Result<Inode> {
        if inum <= 0 || inum > self.num_inodes {
            bail!("invalid inode number: {inum}");
        }

        let position = INODE_START_POSITION + (usize::try_from(inum - 1)? * INODE_SIZE);
        let block_number = position / BLOCK_SIZE;
        let offset = position % BLOCK_SIZE;

        let block = self.storage.read_block(block_number.try_into()?)?;
        let inode = &block[offset..offset + INODE_SIZE];

        bincode::deserialize(inode).context("parsing inode")
    }

    /// Writes to the inode at a given inode number.
    pub fn write_inode(&self, inum: InodeNumber, inode: Inode) -> Result<()> {
        if inum <= 0 || inum > self.num_inodes {
            bail!("invalid inode number: {inum}");
        }

        let inode_serialized = bincode::serialize(&inode).context("serializing inode")?;

        let position = INODE_START_POSITION + ((inum - 1) as usize * INODE_SIZE);
        let block_number = position / BLOCK_SIZE;
        let offset = position % BLOCK_SIZE;

        let mut block = self.storage.read_block(block_number.try_into()?)?;
        block[offset..offset + INODE_SIZE].copy_from_slice(&inode_serialized);

        self.storage.write_block(block_number.try_into()?, &block)?;

        Ok(())
    }

    /// Updates the inode at a given inode number with the changes made by the `update_inode`
    /// function.
    pub fn update_inode<F>(&self, inum: InodeNumber, mut update_inode: F) -> Result<()>
    where
        F: FnMut(&mut Inode),
    {
        let mut inode = self.read_inode(inum)?;
        update_inode(&mut inode);
        self.write_inode(inum, inode)
    }

    /// Creates a new entity of type `inode_type` within a given parent directory with a given name.
    /// It also allocates an inode for the new entity.
    fn create(
        &mut self,
        parent_inum: InodeNumber,
        name: &CStr,
        inode_type: InodeType,
    ) -> Result<InodeNumber> {
        let parent_inode = self.read_inode(parent_inum)?;
        ensure!(
            parent_inode.type_ == InodeType::Directory,
            "parent is not a directory: {parent_inum}"
        );

        let new_inum = self
            .assign_free_inode()
            .ok_or(anyhow!("no more free inodes"))? as InodeNumber;
        let new_entry = DirectoryEntry::new(new_inum as i16, name)?;

        let old_reuse = self.read_inode(new_inum)?.reuse;
        let new_inode = Inode::new(inode_type, old_reuse + 1);
        self.write_inode(new_inum, new_inode)?;

        self.add_directory_entry(parent_inum, &new_entry)?;

        Ok(new_inum)
    }

    /// Add a given entry to a directory.
    ///
    /// If it's available, it uses the first free entry in the directory. Else, it grows the
    /// directory file to fit the new entry.
    fn add_directory_entry(
        &mut self,
        parent_inum: InodeNumber,
        entry: &DirectoryEntry,
    ) -> Result<()> {
        let inode = self.read_inode(parent_inum)?;
        ensure!(
            inode.type_ == InodeType::Directory,
            "inode is not a directory: {parent_inum}"
        );

        let entries = self.read_directory_entries(parent_inum)?;
        let free_entry_index = entries.iter().position(|entry| entry.inum == 0);
        let new_entry_index = free_entry_index.unwrap_or(entries.len());

        let offset = new_entry_index * DIRECTORY_ENTRY_SIZE;
        self.add_entry_at_offset(parent_inum, offset, entry)?;

        Ok(())
    }

    /// Reads the entries within a directory.
    ///
    /// Unlike [`Self::read_directory`], it does not perform any filtering for free entries. This
    /// makes it useful when, for example, the position of an entry in the directory file is
    /// important.
    fn read_directory_entries(&self, inum: InodeNumber) -> Result<Vec<DirectoryEntry>> {
        let inode = self.read_inode(inum)?;
        ensure!(
            inode.type_ == InodeType::Directory,
            "inode is not a directory: {inum}"
        );

        let contents = self.read_file(inum, 0, inode.size as usize)?;
        let entry_chunks = contents.chunks_exact(DIRECTORY_ENTRY_SIZE);
        ensure!(
            entry_chunks.remainder().is_empty(),
            "directory size is not a multiple of {DIRECTORY_ENTRY_SIZE}"
        );

        entry_chunks
            .map(bincode::deserialize::<DirectoryEntry>)
            .collect::<Result<Vec<_>, _>>()
            .map_err(Into::into)
    }

    /// Looks for an entry with a given name in a directory. If found, it returns the entry along
    /// with its position in the directory file.
    fn lookup_directory_entry(
        &self,
        parent_inum: InodeNumber,
        name: &CStr,
    ) -> Result<Option<(usize, DirectoryEntry)>> {
        // we use `read_directory_entries` rather than `read_directory` because the latter may
        // result in incorrect offsets because of its filtering
        let entries = self.read_directory_entries(parent_inum)?;
        let index_entry = entries
            .into_iter()
            .enumerate()
            .filter(|(_, entry)| entry.inum != 0)
            .find(|(_, entry)| CString::from(&entry.name) == name.into());
        let offset_entry =
            index_entry.map(|(entry_index, entry)| (entry_index * DIRECTORY_ENTRY_SIZE, entry));

        Ok(offset_entry)
    }

    /// Adds an entry to a directory at the given position in the directory file.
    fn add_entry_at_offset(
        &mut self,
        inum: InodeNumber,
        entry_offset: usize,
        entry: &DirectoryEntry,
    ) -> Result<()> {
        self.write_file(inum, entry_offset, &bincode::serialize(entry)?)?;

        Ok(())
    }

    /// Removes the entry from a directory at the given position in the directory file.
    fn remove_entry_at_offset(&mut self, inum: InodeNumber, entry_offset: usize) -> Result<()> {
        self.add_entry_at_offset(inum, entry_offset, &FREE_DIRECTORY_ENTRY)
    }

    /// Frees any allocated blocks and writes a free inode in place of the original inode.
    fn delete_inode(&mut self, inum: InodeNumber) -> Result<()> {
        let inode = self.read_inode(inum)?;
        let allocated_blocks = self.get_inode_allocated_block_numbers(inode)?;

        allocated_blocks
            .into_iter()
            .for_each(|block| self.mark_block_as_free(block));

        self.mark_inode_as_free(inum)?;

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
        for block_number in &mut inode.direct {
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
                        .write_block(indirect_block_number, &[0; BLOCK_SIZE])?;

                    inode.indirect = indirect_block_number as i32;

                    [0; NUM_INDIRECT]
                }
            };

            for block_number in &mut indirect_block_numbers {
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
            self.storage.write_block(inode.indirect, &indirect_block)?;
        }

        // update the inode with the new direct/indirect blocks
        self.write_inode(inum, inode)?;

        Ok(())
    }

    /// Reads the block at the requested index within a given file.
    fn read_file_block(&self, inode: Inode, n: usize) -> Result<Block> {
        let block_number = self.get_file_block_number(inode, n)?;
        self.storage.read_block(block_number)
    }

    /// Writes to the block at the requested index within a given file.
    fn write_file_block(&self, inode: Inode, n: usize, block: &Block) -> Result<()> {
        let block_number = self.get_file_block_number(inode, n)?;
        self.storage.write_block(block_number, block)
    }

    /// Converts a block index within a given file to the equivalent disk block number.
    fn get_file_block_number(&self, inode: Inode, n: usize) -> Result<BlockNumber> {
        if n > NUM_DIRECT + NUM_INDIRECT {
            bail!("block index exceeds maximum block count");
        }

        let block_numbers = self.get_inode_allocated_block_numbers(inode)?;

        Ok(*block_numbers
            .get(n)
            .ok_or(anyhow!("block index exceeds allocated block count"))?)
    }

    /// Gets the block numbers of the blocks allocated for a given file.
    ///
    /// Currently, this reads blocks until it encounters a zero block number. However, the correct
    /// behaviour would be to ignore block numbers beyond the minimal number of blocks needed to
    /// represent the size of the file.
    fn get_inode_allocated_block_numbers(&self, inode: Inode) -> Result<Vec<BlockNumber>> {
        let direct_blocks = inode
            .direct
            .into_iter()
            .take_while(|b| *b != 0)
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

    /// Interprets an inode's indirect block (if it exists) as an array of block numbers and returns
    /// the resulting block numbers.
    fn get_indirect_block_numbers(
        &self,
        inode: Inode,
    ) -> Result<Option<[BlockNumber; NUM_INDIRECT]>> {
        if inode.indirect == 0 {
            return Ok(None);
        }

        let indirect_blocks = self
            .storage
            .read_block(inode.indirect)?
            .array_chunks::<4>()
            .map(|b| BlockNumber::from_le_bytes(*b))
            .collect::<Vec<_>>()
            .try_into()
            .expect("NUM_DIRECT is defined as BLOCK_SIZE divided by 4");

        Ok(Some(indirect_blocks))
    }

    /// Looks for a free block and, if found, marks it as allocated.
    fn assign_free_block(&mut self) -> Option<BlockNumber> {
        let assigned = self.block_bitmap.first_zero();

        if let Some(block) = assigned {
            self.block_bitmap.set(block, true);
        }

        assigned.map(|n| n.try_into().unwrap())
    }

    /// Marks a block as free.
    fn mark_block_as_free(&mut self, block_number: BlockNumber) {
        self.block_bitmap
            .set(block_number.try_into().unwrap(), false);
    }

    /// Looks for a free inode and, if found, marks it as allocated.
    fn assign_free_inode(&mut self) -> Option<InodeNumber> {
        let assigned = self.inode_bitmap.first_zero();

        if let Some(inode) = assigned {
            self.inode_bitmap.set(inode, true);
        }

        assigned.map(|inum| inum.try_into().unwrap())
    }

    /// Marks an inode as free and overwrites it with an inode of type [`InodeType::Free`].
    fn mark_inode_as_free(&mut self, inum: InodeNumber) -> Result<()> {
        self.inode_bitmap.set(inum as usize, false);

        self.write_inode(inum, FREE_INODE)
    }

    /// Checks the filesystem for consistency. Performs a depth-first traversal of the directory
    /// tree.
    ///
    /// Does not check for the validity of allocated blocks or block reuse. Some checks are
    /// exclusively performed in [`Self::new`].
    fn check_filesystem(&self) -> Result<()> {
        /// The '.' entry, which refers to the current directory.
        const DOT: &CStr = c".";
        /// The '..' entry, which refers to the parent of the current directory.
        const DOT_DOT: &CStr = c"..";

        let root_inode = self.read_inode(ROOT_INODE)?;
        if root_inode.type_ != InodeType::Directory {
            bail!("root inode does not represent a directory");
        }

        let mut queue = vec![ROOT_INODE];
        let mut seen_directories = HashSet::<InodeNumber>::new();
        let mut directory_parents = HashMap::from([(ROOT_INODE, ROOT_INODE)]);

        while let Some(inum) = queue.pop() {
            let inode = self.read_inode(inum)?;
            if inode.type_ == InodeType::Free {
                bail!("directory tree includes free inode");
            }

            if inode.size < 0 {
                bail!("invalid size in inode: {}", inode.size);
            }

            if inode.size > MAX_FILE_SIZE {
                bail!("size in inode is greater than the maximum valid file size");
            }

            if self.get_inode_allocated_block_numbers(inode)?.len() < inode.size_in_blocks() {
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

                for entry in self.read_directory_entries(inum)? {
                    if entry.inum < 0 || entry.inum > self.num_inodes {
                        bail!("invalid inode number in directory entry: {}", entry.inum);
                    }

                    if entry.inum == 0 {
                        // "free directory entry"
                        if entry.name != DirectoryEntryName::default() {
                            warn!("free directory entry has non-empty name");
                        }

                        continue;
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

                    queue.push(entry.inum);
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

    mod create {
        #[test]
        fn test_invalid_parent_inum() {}

        #[test]
        fn test_non_directory_parent() {}

        #[test]
        fn test_no_more_inodes() {}

        #[test]
        fn test_root_child() {}

        #[test]
        fn test_nested_child() {}

        #[test]
        fn test_parent_free_entry() {}

        #[test]
        fn test_parent_no_free_entry() {}

        #[test]
        fn test_parent_no_free_entry_block_boundary() {}
    }

    mod create_file {
        #[test]
        fn test_inode_type() {}

        #[test]
        fn test_inode_size() {}

        #[test]
        fn test_inode_reuse_count() {}
    }

    mod create_directory {
        #[test]
        fn test_inode_type() {}

        #[test]
        fn test_directory_initial_entries() {}

        #[test]
        fn test_directory_free_entries() {}

        #[test]
        fn test_directory_nlink() {}

        #[test]
        fn test_parent_directory_nlink() {}
    }

    mod remove_directory {
        #[test]
        fn test_parent_inode_type() {}

        #[test]
        fn test_entry_inode_type() {}

        #[test]
        fn test_missing_entry() {}

        #[test]
        fn test_rmdir_non_empty_directory() {}

        #[test]
        fn test_rmdir_root_directory() {}

        #[test]
        fn test_rmdir_empty_directory() {}

        #[test]
        fn test_parent_directory_nlink() {}
    }

    mod create_hard_link {
        #[test]
        fn test_link_directory() {}

        #[test]
        fn test_link_free_inode() {}

        #[test]
        fn test_link_invalid_parent() {}

        #[test]
        fn test_link_file_parent() {}

        #[test]
        fn test_link_duplicate_name() {}

        #[test]
        fn test_link_sibling() {}

        #[test]
        fn test_link_parent_sibling() {}

        #[test]
        fn test_nlink_updated() {}
    }

    mod remove_hard_link {
        #[test]
        fn test_unlink_invalid_parent() {}

        #[test]
        fn test_unlink_dot() {}

        #[test]
        fn test_unlink_dot_dot() {}

        #[test]
        fn test_unlink_non_existent_entry() {}

        #[test]
        fn test_unlink_removes_entry() {}

        #[test]
        fn test_unlink_directory() {}

        #[test]
        fn test_unlink_does_not_remove_file_with_links() {}

        #[test]
        fn test_unlink_decrements_nlink() {}

        #[test]
        fn test_unlink_frees_inode() {}

        #[test]
        fn test_unlink_frees_blocks() {}
    }

    mod rename {
        #[test]
        fn test_missing_source_parent() {}

        #[test]
        fn test_invalid_source_parent() {}

        #[test]
        fn test_missing_target_parent() {}

        #[test]
        fn test_invalid_target_parent() {}

        #[test]
        fn test_missing_source_entry() {}

        #[test]
        fn test_non_existent_target() {}

        #[test]
        fn test_target_is_directory() {}

        #[test]
        fn test_existent_target_multiple_links() {}

        #[test]
        fn test_existent_target_only_link() {}

        #[test]
        fn test_source_name_dot() {}

        #[test]
        fn test_source_name_dot_dot() {}

        #[test]
        fn test_target_name_dot() {}

        #[test]
        fn test_target_name_dot_dot() {}

        #[test]
        fn test_same_parents() {}

        #[test]
        fn test_different_parents() {}

        #[test]
        fn test_same_parents_same_names() {}

        #[test]
        fn test_rename_file() {}

        #[test]
        fn test_rename_directory() {}

        #[test]
        fn test_nlink_unchanged() {}
    }

    mod create_symbolic_link {
        #[test]
        fn test_invalid_parent_inode() {}

        #[test]
        fn test_empty_link() {}

        #[test]
        fn test_link_relative_path() {}

        #[test]
        fn test_link_absolute_path() {}

        #[test]
        fn test_link_non_existent_path() {}

        #[test]
        fn test_link_regular_file() {}

        #[test]
        fn test_link_directory() {}

        #[test]
        fn test_link_symbolic_link() {}

        #[test]
        fn test_file_size() {}

        #[test]
        fn test_file_no_trailing_nul() {}
    }

    mod read_symbolic_link {
        #[test]
        fn test_invalid_inum() {}

        #[test]
        fn test_non_symlink() {}

        #[test]
        fn test_non_existent_path() {}

        #[test]
        fn test_long_path() {}
    }
}
