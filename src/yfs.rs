use std::io;
use std::os::linux::fs::MetadataExt;
use std::{fmt, fs::File, os::unix::prelude::FileExt, time::SystemTime};

use anyhow::{Context, Result};
use bitvec::vec::BitVec;
use serde::Deserialize;
use serde_repr::{Deserialize_repr, Serialize_repr};

const SECTOR_SIZE: usize = 512;

/// size of a disk sector in bytes
pub const BLOCK_SIZE: usize = SECTOR_SIZE;

const BOOT_SECTOR_SIZE: usize = SECTOR_SIZE;

/// number of sectors on the disk
const _NUM_SECTORS: usize = 1426;

const INODE_SIZE: usize = 64;
const NUM_DIRECT: usize = 12;

pub type InodeNumber = i16;

#[derive(Debug, Deserialize)]
pub struct DirectoryName([u8; 30]);

impl fmt::Display for DirectoryName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0
            .into_iter()
            .take_while(|c| *c != 0)
            .try_for_each(|c| write!(f, "{}", c as char))
    }
}

#[derive(Debug, Deserialize)]
#[repr(C)]
pub struct DirectoryEntry {
    /// inode number
    pub inum: InodeNumber,
    /// file name (not null-terminated)
    pub name: DirectoryName,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[repr(C)]
pub struct Inode {
    /// file type (e.g., directory or regular)
    pub type_: InodeType,
    /// number of hard links to inode
    pub nlink: i16,
    /// inode reuse count
    pub reuse: i32,
    /// file size in bytes
    pub size: i32,
    /// block #s for 1st NUM_DIRECT blocks
    pub direct: [i32; NUM_DIRECT],
    /// block number of indirect block
    pub indirect: i32,
}

#[derive(Clone, Copy, Debug, Serialize_repr, Deserialize_repr)]
#[repr(i16)]
pub enum InodeType {
    /// This inode is not in use for any file.
    Free = 0,
    /// This inode describes a directory.
    Directory = 1,
    /// This inode describes a regular data file.
    Regular = 2,
    /// This inode describes a symbolic link.
    Symlink = 3,
}

#[derive(Deserialize)]
#[repr(C)]
struct FileSystemHeader {
    num_blocks: i32,
    num_inodes: i32,
    padding: [u8; 14],
}

pub struct YfsDisk {
    pub file: File,
    pub num_blocks: usize,
    pub num_inodes: usize,
    pub block_bitmap: BitVec,
}

impl YfsDisk {
    pub fn from_file(file: File) -> Result<Self> {
        let mut header = vec![0; BLOCK_SIZE];
        let header_block_number = 1;
        let position = header_block_number * BLOCK_SIZE;

        file.read_at(&mut header, position as u64)
            .context("unable to read disk header")?;

        let header: FileSystemHeader =
            bincode::deserialize(&header).context("unable to parse disk header")?;

        let num_blocks = header.num_blocks as usize;
        let num_inodes = header.num_inodes as usize;

        let mut block_bitmap = BitVec::new();
        block_bitmap.resize(num_blocks, false);

        let last_inode_block = 1 + num_inodes / (BLOCK_SIZE / INODE_SIZE);
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
        let position = BOOT_SECTOR_SIZE + (inum as usize * INODE_SIZE);
        let block_number = position / BLOCK_SIZE;
        let offset = position % BLOCK_SIZE;

        let buf = self.get_block(block_number)?;

        bincode::deserialize(&buf[offset..offset + INODE_SIZE]).context("unable to parse inode")
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
            let mut end_position = position - start_offset + BLOCK_SIZE;
            if end_position > end {
                end_position = end;
            }

            let block_index = position / BLOCK_SIZE;
            let block = self.get_file_block(inode, block_index)?;

            data.extend(block[start_offset..end_position - position].iter());

            position = end_position;
        }

        Ok(data)
    }

    pub fn write_file(&mut self, inode: Inode, offset: usize, data: Vec<u8>) -> Result<()> {
        let mut position = offset;
        let end = offset + data.len();

        while position < end {
            let start_offset = position % BLOCK_SIZE;
            let mut end_position = position - start_offset + BLOCK_SIZE;
            if end_position > end {
                end_position = end;
            }

            let block_index = position / BLOCK_SIZE;
            let mut block = self.get_file_block(inode, block_index)?;

            assert_eq!(
                (end_position - position) - start_offset,
                end_position - position
            );

            block.splice(
                start_offset..end_position - position,
                data[position..end_position].iter().cloned(),
            );

            self.write_file_block(inode, block_index, block)?;

            position = end_position;
        }

        Ok(())
    }

    pub fn atime(&self) -> io::Result<SystemTime> {
        self.file.metadata()?.accessed()
    }

    pub fn mtime(&self) -> io::Result<SystemTime> {
        self.file.metadata()?.modified()
    }

    pub fn crtime(&self) -> io::Result<SystemTime> {
        self.file.metadata()?.created()
    }

    pub fn uid(&self) -> io::Result<u32> {
        Ok(self.file.metadata()?.st_uid())
    }

    pub fn gid(&self) -> io::Result<u32> {
        Ok(self.file.metadata()?.st_gid())
    }

    /// Gets the contents of the request block number of the inode.
    ///
    /// Returns a zeroed block if the block number is out of range.
    fn get_file_block(&self, inode: Inode, n: usize) -> Result<Vec<u8>> {
        let block_number = self.get_file_block_number(inode, n);

        match block_number {
            Ok(b) => self.get_block(b),
            Err(_) => Ok(vec![0; BLOCK_SIZE]),
        }
    }

    fn write_file_block(&self, inode: Inode, n: usize, block: Vec<u8>) -> Result<()> {
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

        let block_number: usize = inode
            .indirect
            .try_into()
            .context("converting block number to usize")?;

        let indirect_blocks = self
            .get_block(block_number)?
            .array_windows::<4>()
            .map(|b| u32::from_le_bytes(*b))
            .collect::<Vec<u32>>();

        Ok(indirect_blocks[n - NUM_DIRECT] as usize)
    }

    fn get_block(&self, block_number: usize) -> Result<Vec<u8>> {
        let mut buf = vec![0; BLOCK_SIZE];
        let position = block_number * BLOCK_SIZE;

        self.file
            .read_at(&mut buf, position as u64)
            .context("reading requested block")?;

        Ok(buf)
    }
}
