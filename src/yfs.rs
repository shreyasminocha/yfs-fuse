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
            Inode, InodeNumber, InodeType, INODES_PER_BLOCK, INODE_SIZE, INODE_START_POSITION,
            MAX_FILE_SIZE, NUM_DIRECT, NUM_INDIRECT, ROOT_INODE,
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

        // we need at least the boot sector and the fs header
        ensure!(
            header.num_blocks >= 2,
            "invalid number of blocks: {}",
            header.num_blocks
        );

        // we need at least the root inode
        ensure!(
            header.num_inodes >= 1,
            "invalid number of inodes: {}",
            header.num_inodes
        );

        ensure!(
            header.num_blocks >= (header.num_inodes + 1).div_ceil(INODES_PER_BLOCK as i32),
            "not enough blocks to store inodes"
        );

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
                ensure!(
                    block_number < yfs.num_blocks,
                    "invalid block number: {block_number}"
                );

                let block_number: usize = block_number.try_into()?;

                ensure!(block_number > last_inode_block, "block is used by inodes");

                if yfs.block_bitmap[block_number] {
                    bail!("block number {block_number} is already allocated");
                }

                yfs.block_bitmap.set(block_number, true);
            }

            if inode.indirect != 0 {
                let indirect_block_number: usize = inode.indirect.try_into()?;

                ensure!(
                    inode.indirect >= 0 && indirect_block_number < yfs.num_blocks.try_into()?,
                    "invalid block number: {}",
                    inode.indirect
                );

                ensure!(
                    indirect_block_number > last_inode_block,
                    "block number {} is used by inodes",
                    indirect_block_number
                );

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
        ensure!(inode.type_ != InodeType::Free, "inode is free: {inum}");

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

        ensure!(
            end <= MAX_FILE_SIZE as usize,
            "requested write ends past the maximum supported file size"
        );

        self.grow_file(inum, end)?; // grows file only if necessary

        // we're careful to read the inode *after* potentially growing the file
        // because that operation manipulates the inode
        let mut inode = self.read_inode(inum)?;
        ensure!(inode.type_ != InodeType::Free, "inode is free: {inum}");

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

        let entry_children = self.read_directory(entry.inum)?;
        let entry_children: Vec<_> = entry_children
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
        ensure!(
            inum > 0 && inum <= self.num_inodes,
            "invalid inode number: {inum}"
        );

        let position = INODE_START_POSITION + (usize::try_from(inum - 1)? * INODE_SIZE);
        let block_number = position / BLOCK_SIZE;
        let offset = position % BLOCK_SIZE;

        let block = self.storage.read_block(block_number.try_into()?)?;
        let inode = &block[offset..offset + INODE_SIZE];

        bincode::deserialize(inode).context("parsing inode")
    }

    /// Writes to the inode at a given inode number.
    pub fn write_inode(&mut self, inum: InodeNumber, inode: Inode) -> Result<()> {
        ensure!(
            inum > 0 && inum <= self.num_inodes,
            "invalid inode number: {inum}"
        );

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
    pub fn update_inode<F>(&mut self, inum: InodeNumber, mut update_inode: F) -> Result<()>
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

        let reuse = self.read_inode(new_inum)?.reuse;
        let new_inode = Inode::new(inode_type, reuse);
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

        ensure!(
            self.lookup_entry(parent_inum, CString::from(&entry.name).as_c_str())?
                .is_none(),
            "entry with same name already exists: {}",
            entry.name
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

    /// Frees any allocated blocks and marks the inode as free. Increments the inode's reuse count.
    fn delete_inode(&mut self, inum: InodeNumber) -> Result<()> {
        let inode = self.read_inode(inum)?;
        ensure!(inode.type_ != InodeType::Free, "inode is free: {inum}");

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
        ensure!(inode.type_ != InodeType::Free, "inode is free: {inum}");

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
    fn write_file_block(&mut self, inode: Inode, n: usize, block: &Block) -> Result<()> {
        let block_number = self.get_file_block_number(inode, n)?;
        self.storage.write_block(block_number, block)
    }

    /// Converts a block index within a given file to the equivalent disk block number.
    fn get_file_block_number(&self, inode: Inode, n: usize) -> Result<BlockNumber> {
        if n > NUM_DIRECT + NUM_INDIRECT {
            bail!("block index exceeds maximum block count");
        }

        let block_numbers = self.get_inode_allocated_block_numbers(inode)?;

        Ok(*block_numbers.get(n).ok_or(anyhow!(
            "block index is not less than allocated block count"
        ))?)
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
    /// Increments the inode's reuse count.
    fn mark_inode_as_free(&mut self, inum: InodeNumber) -> Result<()> {
        self.inode_bitmap.set(inum as usize, false);

        let old_reuse = self.read_inode(inum)?.reuse;
        let new_inode = Inode::new(InodeType::Free, old_reuse + 1);

        self.write_inode(inum, new_inode)
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
        ensure!(
            root_inode.type_ == InodeType::Directory,
            "root inode does not represent a directory"
        );

        let mut queue = vec![ROOT_INODE];
        let mut seen_directories = HashSet::<InodeNumber>::new();
        let mut directory_parents = HashMap::from([(ROOT_INODE, ROOT_INODE)]);

        while let Some(inum) = queue.pop() {
            let inode = self.read_inode(inum)?;
            ensure!(
                inode.type_ != InodeType::Free,
                "directory tree includes free inode"
            );

            ensure!(inode.size >= 0, "invalid size in inode: {}", inode.size);

            ensure!(
                inode.size <= MAX_FILE_SIZE,
                "size in inode is greater than the maximum valid file size"
            );

            // todo: later, this check should use `==`
            ensure!(
                inode.size_in_blocks() <= self.get_inode_allocated_block_numbers(inode)?.len(),
                "inode doesn't have enough blocks to store {} bytes",
                inode.size
            );

            if inode.type_ == InodeType::Directory {
                ensure!(
                    !seen_directories.contains(&inum),
                    "directory tree includes loop"
                );

                seen_directories.insert(inum);

                let parent_inum = *directory_parents
                    .get(&inum)
                    .expect("this directory was discovered through the entries of some directory");

                ensure!(
                    inode.size as usize % DIRECTORY_ENTRY_SIZE == 0,
                    "directory size {} is not a multiple of the directory entry size",
                    inode.size
                );

                let mut entry_names: HashSet<CString> = HashSet::new();

                for entry in self.read_directory_entries(inum)? {
                    ensure!(
                        entry.inum >= 0 && entry.inum <= self.num_inodes,
                        "invalid inode number in directory entry: {}",
                        entry.inum
                    );

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

                    ensure!(
                        !entry_names.contains(entry_name),
                        "directory contains duplicate entry: {}",
                        entry.name
                    );
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

                    ensure!(entry_name != c"", "invalid directory entry name: \"\"");

                    let entry_inode = self.read_inode(entry_inum)?;
                    if entry_inode.type_ == InodeType::Directory {
                        directory_parents.insert(entry_inum, inum);
                    }

                    queue.push(entry.inum);
                }

                ensure!(entry_names.contains(DOT), "no '.' entry");
                ensure!(entry_names.contains(DOT_DOT), "no '..' entry");
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::disk_format::directory_entry::MAX_NAME_LEN;
    use crate::storage::YfsDisk;

    use super::*;

    mod validation {
        use super::*;

        #[test]
        fn test_empty_is_valid() {
            let yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            assert!(Yfs::new(yfs.storage).is_ok());
        }

        #[test]
        fn test_invalid_num_inodes() {}

        #[test]
        fn test_negative_num_blocks() {}

        #[test]
        fn test_invalid_direct_block_block() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            yfs.update_inode(ROOT_INODE, |inode| inode.direct[0] = -1)
                .unwrap();

            assert!(Yfs::new(yfs.storage).is_err());
        }

        #[test]
        fn test_invalid_indirect_block_number() {}

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
        fn test_inode_with_negative_size() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();

            yfs.update_inode(inum, |inode| inode.size = -5).unwrap();

            assert!(Yfs::new(yfs.storage).is_err());
        }

        #[test]
        fn test_inode_with_size_exceeding_the_maximum() {}

        #[test]
        fn test_no_root_inode() {
            let yfs_disk = YfsDisk::new([0; BLOCK_SIZE], vec![], vec![]);
            assert!(Yfs::new(yfs_disk).is_err());
        }

        #[test]
        fn test_non_directory_root_inode() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            yfs.update_inode(ROOT_INODE, |inode| inode.type_ = InodeType::Regular)
                .unwrap();

            assert!(Yfs::new(yfs.storage).is_err());
        }

        #[test]
        fn test_directory_invalid_size() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();

            yfs.update_inode(inum, |inode| inode.size = 45).unwrap();

            assert!(Yfs::new(yfs.storage).is_err());
        }

        #[test]
        fn test_directory_invalid_entry_inum() {}

        #[test]
        fn test_directory_entry_free_inode() {}

        #[test]
        fn test_directory_duplicate_entries() {}

        #[test]
        fn test_directory_no_dot() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();

            yfs.write_file(
                inum,
                0, // assumes that '.' is the first entry
                &bincode::serialize(&DirectoryEntry::new(ROOT_INODE, c"foo").unwrap()).unwrap(),
            )
            .unwrap();

            assert!(Yfs::new(yfs.storage).is_err());
        }

        #[test]
        fn test_directory_invalid_dot() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();

            yfs.write_file(
                inum,
                0,
                &bincode::serialize(&DirectoryEntry::new(ROOT_INODE, c".").unwrap()).unwrap(),
            )
            .unwrap();

            assert!(Yfs::new(yfs.storage).is_err());
        }

        #[test]
        fn test_directory_no_dot_dot() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();

            yfs.write_file(
                inum,
                DIRECTORY_ENTRY_SIZE, // assumes that '..' is the second entry
                &bincode::serialize(&DirectoryEntry::new(ROOT_INODE, c"foo").unwrap()).unwrap(),
            )
            .unwrap();

            assert!(Yfs::new(yfs.storage).is_err());
        }

        #[test]
        fn test_directory_invalid_dot_dot() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();

            yfs.write_file(
                inum,
                DIRECTORY_ENTRY_SIZE,
                &bincode::serialize(&DirectoryEntry::new(inum, c"..").unwrap()).unwrap(),
            )
            .unwrap();

            assert!(Yfs::new(yfs.storage).is_err());
        }

        #[test]
        fn test_directory_loop() {}
    }

    mod read_directory {
        use super::*;

        #[test]
        fn test_invalid_inum() {
            let yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            assert!(yfs.read_directory(5).is_err());
        }

        #[test]
        fn test_non_directory() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();

            assert!(yfs.read_directory(inum).is_err());
        }

        #[test]
        fn test_empty_directory() {
            let yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let entries = yfs.read_directory(ROOT_INODE).unwrap();

            assert_eq!(
                entries,
                vec![
                    DirectoryEntry::new(ROOT_INODE, c".").unwrap(),
                    DirectoryEntry::new(ROOT_INODE, c"..").unwrap(),
                ]
            );
        }

        #[test]
        fn test_some_entries() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            let entries = [
                // invalid, but good enough
                DirectoryEntry::new(5, c"foo").unwrap(),
                DirectoryEntry::new(6, c"bar").unwrap(),
            ];
            yfs.write_file(
                ROOT_INODE,
                2 * DIRECTORY_ENTRY_SIZE,
                &entries
                    .iter()
                    .map(|entry| bincode::serialize(&entry).unwrap())
                    .collect::<Vec<_>>()
                    .concat(),
            )
            .unwrap();

            let read_entries = yfs.read_directory(ROOT_INODE).unwrap();
            assert!(entries.iter().all(|entry| read_entries.contains(entry)));
        }

        #[test]
        fn test_maximum_number_of_entries() {
            let mut yfs = Yfs::new(YfsDisk::empty(2500, 2500).unwrap()).unwrap();
            let existing_entries = yfs.read_directory(ROOT_INODE).unwrap();
            let max_entries = (MAX_FILE_SIZE as usize).div_floor(DIRECTORY_ENTRY_SIZE);

            for i in 0..(max_entries - existing_entries.len()) {
                let name = CString::new(i.to_string()).unwrap();
                let _ = yfs.create_file(ROOT_INODE, &name).unwrap();
            }

            let entries = yfs.read_directory(ROOT_INODE).unwrap();
            assert_eq!(entries.len(), max_entries);
        }

        #[test]
        fn test_entries_past_size() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            let entry = DirectoryEntry::new(5, c"foo").unwrap(); // invalid, but good enough
            yfs.write_file(
                ROOT_INODE,
                2 * DIRECTORY_ENTRY_SIZE,
                &bincode::serialize(&entry).unwrap(),
            )
            .unwrap();

            yfs.update_inode(ROOT_INODE, |inode| {
                inode.size = 2 * DIRECTORY_ENTRY_SIZE as i32
            })
            .unwrap();

            assert!(!yfs.read_directory(ROOT_INODE).unwrap().contains(&entry));
        }

        #[test]
        fn test_free_entries_are_filtered() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            let entries = [
                // invalid, but good enough
                DirectoryEntry::new(0, c"foo").unwrap(),
                DirectoryEntry::new(0, c"bar").unwrap(),
                DirectoryEntry::new(6, c"baz").unwrap(),
                DirectoryEntry::new(0, c"yee").unwrap(),
                DirectoryEntry::new(7, c"haw").unwrap(),
            ];
            yfs.write_file(
                ROOT_INODE,
                2 * DIRECTORY_ENTRY_SIZE,
                &entries
                    .iter()
                    .map(|entry| bincode::serialize(&entry).unwrap())
                    .collect::<Vec<_>>()
                    .concat(),
            )
            .unwrap();

            let read_entries = yfs.read_directory(ROOT_INODE).unwrap();

            assert!(entries
                .iter()
                .filter(|entry| entry.inum != 0)
                .all(|entry| read_entries.contains(entry)));

            assert!(read_entries.iter().all(|entry| entry.inum != 0));
        }
    }

    mod lookup_entry {
        use super::*;

        #[test]
        fn test_invalid_inum() {
            let yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            assert!(yfs.lookup_entry(5, c"foo").is_err());
        }

        #[test]
        fn test_non_directory() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();

            assert!(yfs.lookup_entry(inum, c"bar").is_err());
        }

        #[test]
        fn test_entry_missing() {
            let yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            assert!(yfs.lookup_entry(ROOT_INODE, c"foo").unwrap().is_none());
        }

        #[test]
        fn test_entry_dot() {
            let yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            assert_eq!(
                yfs.lookup_entry(ROOT_INODE, c".").unwrap().unwrap(),
                ROOT_INODE
            );
        }

        #[test]
        fn test_entry_dot_dot() {
            let yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            assert_eq!(
                yfs.lookup_entry(ROOT_INODE, c"..").unwrap().unwrap(),
                ROOT_INODE
            );
        }

        #[test]
        fn test_entry_present() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let foo_inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();
            let bar_inum = yfs.create_file(foo_inum, c"bar").unwrap();

            assert_eq!(
                yfs.lookup_entry(foo_inum, c"bar").unwrap().unwrap(),
                bar_inum
            );
        }

        #[test]
        fn test_entries_several_blocks_in() {
            let mut yfs = Yfs::new(YfsDisk::empty(100, 100).unwrap()).unwrap();
            let num_entries = 5 * DIRECTORY_ENTRIES_PER_BLOCK;

            for i in 0..num_entries {
                let name = CString::new(i.to_string()).unwrap();
                let inum = yfs.create_file(ROOT_INODE, &name).unwrap();

                assert_eq!(yfs.lookup_entry(ROOT_INODE, &name).unwrap().unwrap(), inum);
            }
        }

        #[test]
        fn test_entry_with_zero_inode() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            let fake_entry = DirectoryEntry::new(0, c"foo").unwrap();
            yfs.write_file(
                ROOT_INODE,
                2 * DIRECTORY_ENTRY_SIZE,
                &bincode::serialize(&fake_entry).unwrap(),
            )
            .unwrap();

            assert!(yfs.lookup_entry(ROOT_INODE, c"foo").unwrap().is_none());
        }

        #[test]
        fn test_entry_after_free_entries() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            let fake_entry = DirectoryEntry::new(0, c"foo").unwrap();
            let actual_entry = DirectoryEntry::new(5, c"bar").unwrap(); // still invalid, but good enough
            yfs.write_file(
                ROOT_INODE,
                2 * DIRECTORY_ENTRY_SIZE,
                &[
                    bincode::serialize(&fake_entry).unwrap(),
                    bincode::serialize(&actual_entry).unwrap(),
                ]
                .concat(),
            )
            .unwrap();

            assert_eq!(yfs.lookup_entry(ROOT_INODE, c"bar").unwrap().unwrap(), 5);
        }

        #[test]
        fn test_entry_past_size() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            let entry = DirectoryEntry::new(5, c"foo").unwrap(); // invalid, but good enough
            yfs.write_file(
                ROOT_INODE,
                2 * DIRECTORY_ENTRY_SIZE,
                &bincode::serialize(&entry).unwrap(),
            )
            .unwrap();
            assert!(yfs.lookup_entry(ROOT_INODE, c"foo").unwrap().is_some());

            yfs.update_inode(ROOT_INODE, |inode| {
                inode.size = 2 * DIRECTORY_ENTRY_SIZE as i32
            })
            .unwrap();
            assert!(yfs.lookup_entry(ROOT_INODE, c"foo").unwrap().is_none());
        }
    }

    mod create {
        use super::*;

        #[test]
        fn test_invalid_parent_inum() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            assert!(yfs.create(2, c"foo", InodeType::Regular).is_err());
        }

        #[test]
        fn test_non_directory_parent() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let parent_inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();

            assert!(yfs.create(parent_inum, c"bar", InodeType::Regular).is_err());
        }

        #[test]
        fn test_name_length_at_limit() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let name = CString::new("a".repeat(MAX_NAME_LEN)).unwrap();

            assert!(yfs.create(ROOT_INODE, &name, InodeType::Regular).is_ok());
        }

        #[test]
        fn test_name_too_long() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let name = CString::new("a".repeat(MAX_NAME_LEN + 1)).unwrap();

            assert!(yfs.create(ROOT_INODE, &name, InodeType::Regular).is_err());
        }

        #[test]
        fn test_no_more_inodes() {
            let mut yfs = Yfs::new(YfsDisk::empty(1, 10).unwrap()).unwrap();

            assert!(yfs.create(ROOT_INODE, c"foo", InodeType::Regular).is_err());
        }

        #[test]
        fn test_entry_already_exists() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let _ = yfs.create(ROOT_INODE, c"foo", InodeType::Regular);

            assert!(yfs.create(ROOT_INODE, c"foo", InodeType::Regular).is_err());
        }

        #[test]
        fn test_root_child() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create(ROOT_INODE, c"foo", InodeType::Regular).unwrap();
            let root_entries = yfs.read_directory(ROOT_INODE).unwrap();

            assert!(root_entries.iter().any(|entry| entry.inum == inum));
        }

        #[test]
        fn test_nested_child() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let parent_inum = yfs.create_directory(ROOT_INODE, c"a").unwrap();
            let parent_inum = yfs.create_directory(parent_inum, c"a").unwrap();
            let parent_inum = yfs.create_directory(parent_inum, c"a").unwrap();
            let parent_inum = yfs.create_directory(parent_inum, c"a").unwrap();
            let parent_inum = yfs.create_directory(parent_inum, c"a").unwrap();

            // /a/a/a/a/a/foo
            let inum = yfs.create(parent_inum, c"foo", InodeType::Regular).unwrap();
            let parent_entries = yfs.read_directory(parent_inum).unwrap();
            assert!(parent_entries.iter().any(|entry| entry.inum == inum));
        }

        #[test]
        fn test_reuse_free_entry() {
            let mut yfs = Yfs::new(YfsDisk::empty(20, 10).unwrap()).unwrap();
            let existing_entries = yfs.read_directory(ROOT_INODE).unwrap();

            for i in 0..(DIRECTORY_ENTRIES_PER_BLOCK - existing_entries.len()) {
                let name = CString::new(i.to_string()).unwrap();
                let _ = yfs.create_file(ROOT_INODE, &name).unwrap();
            }

            let root_inode = yfs.read_inode(ROOT_INODE).unwrap();
            let root_inode_allocated_blocks =
                yfs.get_inode_allocated_block_numbers(root_inode).unwrap();
            assert_eq!(root_inode_allocated_blocks.len(), 1);

            let (entry_offset, _) = yfs
                .lookup_directory_entry(ROOT_INODE, c"4")
                .unwrap()
                .unwrap();
            yfs.remove_hard_link(ROOT_INODE, c"4").unwrap();

            let _ = yfs.create(ROOT_INODE, c"foo", InodeType::Regular).unwrap();

            assert_eq!(
                yfs.lookup_directory_entry(ROOT_INODE, c"foo")
                    .unwrap()
                    .unwrap()
                    .0,
                entry_offset
            );
        }

        #[test]
        fn test_grow_when_no_free_entry() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            yfs.update_inode(ROOT_INODE, |inode| {
                inode.size = 2 * DIRECTORY_ENTRY_SIZE as i32
            })
            .unwrap();

            let inum = yfs.create(ROOT_INODE, c"foo", InodeType::Regular).unwrap();
            let root_entries = yfs.read_directory(ROOT_INODE).unwrap();
            assert!(root_entries.iter().any(|entry| entry.inum == inum));

            let root_inode = yfs.read_inode(ROOT_INODE).unwrap();
            assert!(root_inode.size > 2 * DIRECTORY_ENTRY_SIZE as i32);
        }

        #[test]
        fn test_parent_no_free_entry_block_boundary() {
            let mut yfs = Yfs::new(YfsDisk::empty(20, 10).unwrap()).unwrap();
            let existing_entries = yfs.read_directory(ROOT_INODE).unwrap();

            for i in 0..(DIRECTORY_ENTRIES_PER_BLOCK - existing_entries.len()) {
                let name = CString::new(i.to_string()).unwrap();
                let _ = yfs.create_file(ROOT_INODE, &name).unwrap();
            }

            let root_inode = yfs.read_inode(ROOT_INODE).unwrap();
            let root_inode_allocated_blocks =
                yfs.get_inode_allocated_block_numbers(root_inode).unwrap();
            assert_eq!(root_inode_allocated_blocks.len(), 1);

            let inum = yfs.create(ROOT_INODE, c"foo", InodeType::Regular).unwrap();
            let entries = yfs.read_directory(ROOT_INODE).unwrap();
            assert!(entries.iter().any(|entry| entry.inum == inum));

            let root_inode = yfs.read_inode(ROOT_INODE).unwrap();
            let root_inode_allocated_blocks =
                yfs.get_inode_allocated_block_numbers(root_inode).unwrap();
            assert_eq!(root_inode_allocated_blocks.len(), 2);
        }

        #[test]
        fn test_parent_at_entry_limit() {
            let mut yfs = Yfs::new(YfsDisk::empty(2500, 2500).unwrap()).unwrap();
            let existing_entries = yfs.read_directory(ROOT_INODE).unwrap();
            let max_entries = (MAX_FILE_SIZE as usize).div_floor(DIRECTORY_ENTRY_SIZE);

            for i in 0..(max_entries - existing_entries.len()) {
                let name = CString::new(i.to_string()).unwrap();
                let _ = yfs.create_file(ROOT_INODE, &name).unwrap();
            }

            assert!(yfs.create(ROOT_INODE, c"foo", InodeType::Regular).is_err());
        }

        #[test]
        fn test_inode_reuse_count_fresh() {
            let mut yfs = Yfs::new(YfsDisk::empty(2, 10).unwrap()).unwrap();
            let inum = yfs.create(ROOT_INODE, c"foo", InodeType::Regular).unwrap();
            let inode = yfs.read_inode(inum).unwrap();

            assert_eq!(inode.reuse, 0);
        }

        #[test]
        fn test_inode_reuse_count_reused() {
            let mut yfs = Yfs::new(YfsDisk::empty(2, 10).unwrap()).unwrap();
            let inum = yfs.create(ROOT_INODE, c"foo", InodeType::Regular).unwrap();
            let inode = yfs.read_inode(inum).unwrap();
            assert_eq!(inode.reuse, 0);

            yfs.remove_hard_link(ROOT_INODE, c"foo").unwrap();
            let inum = yfs.create(ROOT_INODE, c"foo", InodeType::Regular).unwrap();
            let inode = yfs.read_inode(inum).unwrap();
            assert_eq!(inode.reuse, 1);
        }
    }

    mod create_file {
        use super::*;

        #[test]
        fn test_inode_type() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            let inode = yfs.read_inode(inum).unwrap();

            assert_eq!(inode.type_, InodeType::Regular);
        }

        #[test]
        fn test_inode_size() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            let inode = yfs.read_inode(inum).unwrap();

            assert_eq!(inode.size, 0);
        }

        #[test]
        fn test_nlink() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            let inode = yfs.read_inode(inum).unwrap();

            assert_eq!(inode.nlink, 1);
        }
    }

    mod create_directory {
        use super::*;

        #[test]
        fn test_inode_type() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();
            let inode = yfs.read_inode(inum).unwrap();

            assert_eq!(inode.type_, InodeType::Directory);
        }

        #[test]
        fn test_directory_initial_entries() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();
            let entries = yfs.read_directory(inum).unwrap();

            assert_eq!(
                entries,
                vec![
                    DirectoryEntry::new(inum, c".").unwrap(),
                    DirectoryEntry::new(ROOT_INODE, c"..").unwrap()
                ]
            );
        }

        #[test]
        fn test_allocated_block_has_garbage() {
            let mut yfs = Yfs::new(YfsDisk::empty(7, 2).unwrap()).unwrap();
            let entries_block_number = 3;
            yfs.storage
                .write_block(entries_block_number, &[0xff; BLOCK_SIZE])
                .unwrap();

            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();
            let inode = yfs.read_inode(inum).unwrap();
            assert_eq!(inode.direct[0], entries_block_number);

            let entries = yfs.read_directory(inum).unwrap();
            assert_eq!(entries.len(), 2);
        }

        #[test]
        fn test_directory_nlink() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();
            let inode = yfs.read_inode(inum).unwrap();

            assert_eq!(inode.nlink, 2);
        }

        #[test]
        fn test_parent_directory_nlink() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let root_inode = yfs.read_inode(ROOT_INODE).unwrap();
            assert_eq!(root_inode.nlink, 2);

            let _ = yfs.create_directory(ROOT_INODE, c"foo").unwrap();
            let root_inode = yfs.read_inode(ROOT_INODE).unwrap();
            assert_eq!(root_inode.nlink, 3);
        }
    }

    mod remove_directory {
        use super::*;

        #[test]
        fn test_file_parent() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();

            assert!(yfs.remove_directory(inum, c"bar").is_err());
        }

        #[test]
        fn test_file_entry() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let _ = yfs.create_file(ROOT_INODE, c"foo");

            assert!(yfs.remove_directory(ROOT_INODE, c"foo").is_err());
        }

        #[test]
        fn test_missing_entry() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let _ = yfs.create_directory(ROOT_INODE, c"foo");

            assert!(yfs.remove_directory(ROOT_INODE, c"bar").is_err());
        }

        #[test]
        fn test_rmdir_non_empty_directory() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();

            let _ = yfs.create_file(inum, c"a").unwrap();
            let _ = yfs.create_file(inum, c"b").unwrap();
            let _ = yfs.create_file(inum, c"c").unwrap();

            assert!(yfs.remove_directory(ROOT_INODE, c"foo").is_err());
        }

        #[test]
        fn test_rmdir_root_directory() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            assert!(yfs.remove_directory(ROOT_INODE, c".").is_err());
        }

        #[test]
        fn test_rmdir_empty_directory() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();

            yfs.remove_directory(ROOT_INODE, c"foo").unwrap();

            let root_entries = yfs.read_directory(ROOT_INODE).unwrap();
            assert!(root_entries.iter().all(|entry| entry.inum != inum));
        }

        #[test]
        fn test_rmdir_nested_directory() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let parent_inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();
            let parent_inum = yfs.create_directory(parent_inum, c"bar").unwrap();
            let inum = yfs.create_directory(parent_inum, c"baz").unwrap();

            yfs.remove_directory(parent_inum, c"baz").unwrap();

            let root_entries = yfs.read_directory(parent_inum).unwrap();
            assert!(root_entries.iter().all(|entry| entry.inum != inum));
        }

        #[test]
        fn test_parent_directory_nlink() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let _ = yfs.create_directory(ROOT_INODE, c"foo").unwrap();

            let old_nlink = yfs.read_inode(ROOT_INODE).unwrap().nlink;
            yfs.remove_directory(ROOT_INODE, c"foo").unwrap();
            let new_nlink = yfs.read_inode(ROOT_INODE).unwrap().nlink;

            assert_eq!(new_nlink, old_nlink - 1);
        }
    }

    mod create_hard_link {
        use super::*;

        #[test]
        fn test_link_directory() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_directory(ROOT_INODE, c"foo").unwrap();

            assert!(yfs.create_hard_link(ROOT_INODE, c"bar", inum).is_err());
        }

        #[test]
        fn test_link_free_inode() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            assert!(yfs.create_hard_link(ROOT_INODE, c"foo", 2).is_err());
        }

        #[test]
        fn test_invalid_parent() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();

            assert!(yfs.create_hard_link(2, c"foo", inum).is_err());
        }

        #[test]
        fn test_link_file_parent() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let foo_inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            let bar_inum = yfs.create_file(ROOT_INODE, c"bar").unwrap();

            assert!(yfs.create_hard_link(foo_inum, c"baz", bar_inum).is_err());
        }

        #[test]
        fn test_link_duplicate_name() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let foo_inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            let _ = yfs.create_file(ROOT_INODE, c"bar").unwrap();

            assert!(yfs.create_hard_link(ROOT_INODE, c"bar", foo_inum).is_err());
        }

        #[test]
        fn test_link_sibling() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let foo_inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            yfs.create_hard_link(ROOT_INODE, c"bar", foo_inum).unwrap();

            let foo_inum = yfs.lookup_entry(ROOT_INODE, c"foo").unwrap().unwrap();
            let bar_inum = yfs.lookup_entry(ROOT_INODE, c"bar").unwrap().unwrap();

            assert_eq!(foo_inum, bar_inum);
        }

        #[test]
        fn test_link_non_sibling() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let foo_inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            let parent_inum = yfs.create_directory(ROOT_INODE, c"a").unwrap();
            let parent_inum = yfs.create_directory(parent_inum, c"b").unwrap();
            let parent_inum = yfs.create_directory(parent_inum, c"c").unwrap();

            yfs.create_hard_link(parent_inum, c"bar", foo_inum).unwrap();

            let foo_inum = yfs.lookup_entry(ROOT_INODE, c"foo").unwrap().unwrap();
            let bar_inum = yfs.lookup_entry(parent_inum, c"bar").unwrap().unwrap();

            assert_eq!(foo_inum, bar_inum);
        }

        #[test]
        fn test_nlink_updated() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();

            let old_nlink = yfs.read_inode(inum).unwrap().nlink;
            yfs.create_hard_link(ROOT_INODE, c"bar", inum).unwrap();
            let new_nlink = yfs.read_inode(inum).unwrap().nlink;

            assert_eq!(new_nlink, old_nlink + 1);
        }
    }

    mod remove_hard_link {
        use super::*;

        #[test]
        fn test_invalid_parent() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            let _ = yfs.create_hard_link(ROOT_INODE, c"bar", inum);

            assert!(yfs.remove_hard_link(2, c"bar").is_err());
        }

        #[test]
        fn test_unlink_dot() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            assert!(yfs.remove_hard_link(ROOT_INODE, c".").is_err());
        }

        #[test]
        fn test_unlink_dot_dot() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            assert!(yfs.remove_hard_link(ROOT_INODE, c"..").is_err());
        }

        #[test]
        fn test_unlink_non_existent_entry() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();

            assert!(yfs.remove_hard_link(ROOT_INODE, c"foo").is_err());
        }

        #[test]
        fn test_unlink_directory() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let _ = yfs.create_directory(ROOT_INODE, c"foo");

            assert!(yfs.remove_hard_link(2, c"foo").is_err());
        }

        #[test]
        fn test_removes_entry() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let _ = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            assert!(yfs.lookup_entry(ROOT_INODE, c"foo").unwrap().is_some());

            yfs.remove_hard_link(ROOT_INODE, c"foo").unwrap();
            assert!(yfs.lookup_entry(ROOT_INODE, c"foo").unwrap().is_none());
        }

        #[test]
        fn test_does_not_remove_file_with_links() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            let data = b"stuff";
            yfs.write_file(inum, 0, data).unwrap();

            yfs.create_hard_link(ROOT_INODE, c"bar", inum).unwrap();
            yfs.remove_hard_link(ROOT_INODE, c"bar").unwrap();

            assert_eq!(yfs.read_file(inum, 0, 512).unwrap(), data);
        }

        #[test]
        fn test_removes_file_without_links() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            yfs.write_file(inum, 0, b"stuff").unwrap();

            yfs.remove_hard_link(ROOT_INODE, c"foo").unwrap();

            assert!(yfs.read_file(inum, 0, 512).is_err());
        }

        #[test]
        fn test_remove_created_link() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();

            yfs.create_hard_link(ROOT_INODE, c"bar", inum).unwrap();
            assert!(yfs.lookup_entry(ROOT_INODE, c"bar").unwrap().is_some());

            yfs.remove_hard_link(ROOT_INODE, c"bar").unwrap();

            assert!(yfs.lookup_entry(ROOT_INODE, c"bar").unwrap().is_none());
            assert!(yfs.lookup_entry(ROOT_INODE, c"foo").unwrap().is_some());
        }

        #[test]
        fn test_remove_original() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();

            yfs.create_hard_link(ROOT_INODE, c"bar", inum).unwrap();
            assert!(yfs.lookup_entry(ROOT_INODE, c"bar").unwrap().is_some());

            yfs.remove_hard_link(ROOT_INODE, c"foo").unwrap();

            assert!(yfs.lookup_entry(ROOT_INODE, c"foo").unwrap().is_none());
            assert!(yfs.lookup_entry(ROOT_INODE, c"bar").unwrap().is_some());
        }

        #[test]
        fn test_decrements_nlink() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 10).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            yfs.create_hard_link(ROOT_INODE, c"bar", inum).unwrap();

            let old_nlink = yfs.read_inode(inum).unwrap().nlink;
            yfs.remove_hard_link(ROOT_INODE, c"foo").unwrap();
            let new_nlink = yfs.read_inode(inum).unwrap().nlink;

            assert_eq!(new_nlink, old_nlink - 1);
        }

        #[test]
        fn test_frees_inode() {
            let mut yfs = Yfs::new(YfsDisk::empty(2, 10).unwrap()).unwrap();
            let _ = yfs.create_file(ROOT_INODE, c"foo").unwrap();

            assert!(yfs.create_file(ROOT_INODE, c"bar").is_err());

            yfs.remove_hard_link(ROOT_INODE, c"foo").unwrap();

            assert!(yfs.create_file(ROOT_INODE, c"bar").is_ok());
        }

        #[test]
        fn test_frees_blocks() {
            let mut yfs = Yfs::new(YfsDisk::empty(10, 2).unwrap()).unwrap();
            let inum = yfs.create_file(ROOT_INODE, c"foo").unwrap();
            yfs.write_file(inum, 0, b"stuff").unwrap();

            assert_eq!(yfs.num_free_blocks(), 0);
            assert!(yfs.create_directory(ROOT_INODE, c"bar").is_err());

            yfs.remove_hard_link(ROOT_INODE, c"foo").unwrap();
            assert!(yfs.num_free_blocks() > 0);

            assert!(yfs.create_directory(ROOT_INODE, c"baz").is_ok());
        }
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
