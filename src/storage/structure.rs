use std::ops::Range;

use anyhow::{bail, ensure, Context, Result};

use crate::disk_format::{
    block::{Block, BlockNumber, BLOCK_SIZE},
    header::{FileSystemHeader, FS_HEADER_SIZE},
    inode::{Inode, INODES_PER_BLOCK, INODE_SIZE},
};

use super::yfs_storage::YfsStorage;

/// A YFS disk with `I` inodes and `D` data blocks.
pub struct YfsDisk<const I: usize, const D: usize> {
    /// The boot block.
    boot_sector: Block,
    /// The file system header.
    file_system_header: FileSystemHeader,
    /// The inodes.
    pub inodes: [Inode; I],
    /// The blocks that hold file data.
    pub data_blocks: [Block; D],
}

impl<const I: usize, const D: usize> YfsDisk<I, D> {
    // we add one because the first INODE_SIZE bytes in the first inode block are occupied by the
    // file system header
    /// The number of blocks occupied by inodes.
    pub const NUM_INODE_BLOCKS: usize = (I + 1).div_ceil(INODES_PER_BLOCK);

    /// The total number of blocks in the disk including the boot block, blocks occupied by inodes,
    /// and data blocks.
    pub const NUM_BLOCKS: usize = 1 + Self::NUM_INODE_BLOCKS + D;

    /// Constructs a new [`YfsDisk`] instance.
    #[must_use]
    pub fn new(boot_sector: Block, inodes: [Inode; I], data_blocks: [Block; D]) -> Self {
        let file_system_header = FileSystemHeader::new(Self::NUM_BLOCKS as i32, I as i32);

        Self {
            boot_sector,
            file_system_header,
            inodes,
            data_blocks,
        }
    }

    /// Calculates the range of inodes contained within a block, if any.
    fn get_inode_range(block_number: BlockNumber) -> Result<Range<usize>> {
        let block_number = usize::try_from(block_number)?;

        ensure!(
            block_number >= 1 && block_number <= Self::NUM_INODE_BLOCKS,
            "block number does not point to an inode block"
        );

        if block_number == 1 {
            Ok(0..(INODES_PER_BLOCK - 1).min(I))
        } else {
            let start = ((block_number - 1) * INODES_PER_BLOCK) - 1;
            let end = ((block_number * INODES_PER_BLOCK) - 1).min(I);

            Ok(start..end)
        }
    }

    /// Attempts to convert a block number into an index into the data blocks.
    fn block_number_to_data_block_number(block_number: BlockNumber) -> Result<Option<usize>> {
        let block_number = usize::try_from(block_number)?;

        if block_number > Self::NUM_INODE_BLOCKS {
            Ok(Some(block_number - Self::NUM_INODE_BLOCKS - 1))
        } else {
            Ok(None)
        }
    }
}

impl<const I: usize, const D: usize> YfsStorage for YfsDisk<I, D> {
    fn read_block(&self, block_number: BlockNumber) -> Result<Block> {
        ensure!(block_number >= 0, "invalid block number: {block_number}");

        let block = match usize::try_from(block_number)? {
            0 => self.boot_sector,
            1 => {
                let header_serialized = bincode::serialize(&self.file_system_header)?;

                let inodes = &self.inodes[Self::get_inode_range(block_number)?];
                let inodes_serialized = serialize_inodes(inodes)?;

                let mut block = [header_serialized, inodes_serialized].concat();
                block.resize(BLOCK_SIZE, 0);

                block
                    .try_into()
                    .expect("we resized the vector to BLOCK_SIZE")
            }
            b if b >= 2 && b <= Self::NUM_INODE_BLOCKS => {
                let inodes = &self.inodes[Self::get_inode_range(block_number)?];

                let mut block = serialize_inodes(inodes)?;
                block.resize(BLOCK_SIZE, 0);

                block
                    .try_into()
                    .expect("we resized the vector to BLOCK_SIZE")
            }
            b if b > Self::NUM_INODE_BLOCKS && b < Self::NUM_BLOCKS => {
                self.data_blocks[Self::block_number_to_data_block_number(block_number)?
                    .expect("we get here only if it's a data block")]
            }
            _ => bail!("block number out of bounds"),
        };

        Ok(block)
    }

    fn write_block(&mut self, block_number: BlockNumber, block: &Block) -> Result<()> {
        ensure!(block_number >= 0, "invalid block number: {block_number}");

        match usize::try_from(block_number)? {
            0 => {
                self.boot_sector = *block;
            }
            1 => {
                self.file_system_header = bincode::deserialize(&block[0..FS_HEADER_SIZE])?;

                let inode_bytes = &block[FS_HEADER_SIZE..];
                let inodes: Vec<Inode> = deserialize_inodes(inode_bytes)?;

                let inode_range = Self::get_inode_range(block_number)?;
                let num_inodes = inode_range.len();
                self.inodes[inode_range].copy_from_slice(&inodes[..num_inodes]);
            }
            b if b >= 2 && b <= Self::NUM_INODE_BLOCKS => {
                let inodes: Vec<Inode> = deserialize_inodes(block)?;

                let inode_range = Self::get_inode_range(block_number)?;
                let num_inodes = inode_range.len();
                self.inodes[inode_range].copy_from_slice(&inodes[..num_inodes]);
            }
            b if b > Self::NUM_INODE_BLOCKS && b < Self::NUM_BLOCKS => {
                let data_block_number = Self::block_number_to_data_block_number(block_number)?
                    .expect("we get here only if it's a data block");
                self.data_blocks[data_block_number] = *block;
            }
            _ => bail!("block number out of bounds"),
        };

        Ok(())
    }
}

/// Serialize a slice of inodes.
fn serialize_inodes(inodes: &[Inode]) -> Result<Vec<u8>> {
    Ok(inodes
        .iter()
        .map(|inode| bincode::serialize(inode).context("serializing inode"))
        .collect::<Result<Vec<_>>>()?
        .concat())
}

/// Deserialize a slice of bytes into inodes.
fn deserialize_inodes(bytes: &[u8]) -> Result<Vec<Inode>> {
    bytes
        .array_chunks::<INODE_SIZE>()
        .map(|chunk| bincode::deserialize(chunk).context("deserializing inode"))
        .collect::<Result<Vec<_>>>()
}

#[cfg(test)]
mod tests {
    use crate::disk_format::{
        block::BLOCK_SIZE,
        header::FS_HEADER_SIZE,
        inode::{Inode, InodeType, FREE_INODE, INODES_PER_BLOCK, INODE_SIZE, NUM_DIRECT},
    };

    use super::*;

    #[test]
    fn test_file_system_header() {
        let yfs_disk = YfsDisk::new(EMPTY_BLOCK, [FREE_INODE], [EMPTY_BLOCK, EMPTY_BLOCK]);

        assert_eq!(yfs_disk.file_system_header.num_inodes, 1);
        assert_eq!(yfs_disk.file_system_header.num_blocks, 1 + 1 + 2);
    }

    #[test]
    fn test_num_blocks_no_inodes() {
        let yfs_disk = YfsDisk::new(EMPTY_BLOCK, [], []);

        assert_eq!(yfs_disk.file_system_header.num_inodes, 0);
        assert_eq!(yfs_disk.file_system_header.num_blocks, 1 + 1);
    }

    #[test]
    fn test_num_inode_blocks_block_boundary() {
        let yfs_disk = YfsDisk::<7, 2>::new(
            EMPTY_BLOCK,
            [FREE_INODE].repeat(7).try_into().unwrap(),
            [EMPTY_BLOCK].repeat(2).try_into().unwrap(),
        );

        assert_eq!(yfs_disk.file_system_header.num_inodes, 7);
        assert_eq!(yfs_disk.file_system_header.num_blocks, 1 + 1 + 2);

        let yfs_disk = YfsDisk::<8, 2>::new(
            EMPTY_BLOCK,
            [FREE_INODE].repeat(8).try_into().unwrap(),
            [EMPTY_BLOCK].repeat(2).try_into().unwrap(),
        );

        assert_eq!(yfs_disk.file_system_header.num_inodes, 8);
        assert_eq!(yfs_disk.file_system_header.num_blocks, 1 + 2 + 2);
    }

    mod read_block {
        use super::*;

        #[test]
        fn test_read_boot_sector() {
            let boot_sector = [0xfe; BLOCK_SIZE];
            let yfs_disk = YfsDisk::new(boot_sector, [FREE_INODE], [EMPTY_BLOCK]);

            assert_eq!(yfs_disk.read_block(0).unwrap(), boot_sector);
        }

        #[test]
        fn test_read_out_of_bounds_block() {
            let yfs_disk = YfsDisk::new(EMPTY_BLOCK, [FREE_INODE], [EMPTY_BLOCK]);
            assert!(yfs_disk.read_block(2).is_ok());
            assert!(yfs_disk.read_block(3).is_err());
            assert!(yfs_disk.read_block(4).is_err());

            let yfs_disk = YfsDisk::new(EMPTY_BLOCK, [FREE_INODE; 7], [EMPTY_BLOCK; 5]);
            assert!(yfs_disk.read_block(6).is_ok());
            assert!(yfs_disk.read_block(7).is_err());
            assert!(yfs_disk.read_block(8).is_err());
        }

        #[test]
        fn test_read_block_one_empty() {
            let yfs_disk = YfsDisk::new(EMPTY_BLOCK, [], [[0xfe; BLOCK_SIZE]]);
            let block_one = yfs_disk.read_block(1).unwrap();

            let header_bytes = &block_one[..FS_HEADER_SIZE];
            let header: FileSystemHeader = bincode::deserialize(header_bytes).unwrap();

            assert_eq!(header.num_inodes, 0);
            assert_eq!(header.num_blocks, 1 + 1 + 1);

            for inode_bytes in block_one.chunks(INODE_SIZE).skip(1) {
                let inode: Inode = bincode::deserialize(inode_bytes).unwrap();
                assert_eq!(inode.type_, InodeType::Free);
            }
        }

        #[test]
        fn test_read_block_one_incomplete() {
            let inodes = [EMPTY_DIRECTORY_INODE, EMPTY_FILE_INODE, EMPTY_FILE_INODE];
            let num_inodes = inodes.len();

            let yfs_disk = YfsDisk::new(EMPTY_BLOCK, inodes, [[0xfe; BLOCK_SIZE]]);

            let block_one = yfs_disk.read_block(1).unwrap();
            for (i, inode_bytes) in block_one.chunks(INODE_SIZE).skip(1).enumerate() {
                let inode: Inode = bincode::deserialize(inode_bytes).unwrap();

                if i < num_inodes {
                    assert_eq!(inode, inodes[i]);
                }
            }
        }

        #[test]
        fn test_read_block_one_full() {
            let inodes = [
                EMPTY_DIRECTORY_INODE,
                EMPTY_FILE_INODE,
                EMPTY_FILE_INODE,
                EMPTY_FILE_INODE,
                EMPTY_FILE_INODE,
                EMPTY_FILE_INODE,
                FREE_INODE,
            ];

            let yfs_disk = YfsDisk::new(EMPTY_BLOCK, inodes, [[0xfe; BLOCK_SIZE]]);

            let block_one = yfs_disk.read_block(1).unwrap();
            for (i, inode_bytes) in block_one.chunks(INODE_SIZE).skip(1).enumerate() {
                let inode: Inode = bincode::deserialize(inode_bytes).unwrap();
                assert_eq!(inode, inodes[i]);
            }
        }

        #[test]
        fn test_read_last_inode_block_incomplete() {
            let inodes = [
                EMPTY_DIRECTORY_INODE,
                EMPTY_FILE_INODE,
                EMPTY_FILE_INODE,
                EMPTY_FILE_INODE,
                EMPTY_FILE_INODE,
                EMPTY_FILE_INODE,
                FREE_INODE,
                EMPTY_FILE_INODE,
                EMPTY_DIRECTORY_INODE,
            ];

            let yfs_disk = YfsDisk::new(EMPTY_BLOCK, inodes, [[0xfe; BLOCK_SIZE]]);

            let second_block = yfs_disk.read_block(2).unwrap();
            let second_block_inodes = &inodes[INODES_PER_BLOCK - 1..];

            for (i, inode_bytes) in second_block.chunks(INODE_SIZE).enumerate() {
                let inode: Inode = bincode::deserialize(inode_bytes).unwrap();

                if i < second_block_inodes.len() {
                    assert_eq!(inode, second_block_inodes[i]);
                } else {
                    assert_eq!(inode.type_, InodeType::Free);
                }
            }
        }

        #[test]
        fn test_read_last_inode_block_full() {
            let inodes = [EMPTY_FILE_INODE].repeat(7 + 8);
            let inodes = inodes.as_slice();

            let yfs_disk = YfsDisk::<15, 1>::new(
                EMPTY_BLOCK,
                inodes.try_into().unwrap(),
                [[0xfe; BLOCK_SIZE]],
            );

            let second_block = yfs_disk.read_block(2).unwrap();
            let second_block_inodes = &inodes[INODES_PER_BLOCK - 1..];

            for (i, inode_bytes) in second_block.chunks(INODE_SIZE).enumerate() {
                let inode: Inode = bincode::deserialize(inode_bytes).unwrap();
                assert_eq!(inode, second_block_inodes[i]);
            }
        }

        #[test]
        fn test_read_first_data_block() {
            let inodes = [EMPTY_DIRECTORY_INODE, EMPTY_FILE_INODE, EMPTY_FILE_INODE];
            let data_blocks = [[0xfe; BLOCK_SIZE]];

            let yfs_disk = YfsDisk::new(EMPTY_BLOCK, inodes, data_blocks);

            let block = yfs_disk.read_block(2).unwrap();
            assert_eq!(block, data_blocks[0]);
        }

        #[test]
        fn test_read_last_data_block() {
            let inodes = [
                EMPTY_DIRECTORY_INODE,
                EMPTY_FILE_INODE,
                EMPTY_FILE_INODE,
                FREE_INODE,
                FREE_INODE,
                FREE_INODE,
                FREE_INODE,
                FREE_INODE,
            ];
            let data_blocks = [[0xab; BLOCK_SIZE], [0xcd; BLOCK_SIZE], [0xef; BLOCK_SIZE]];

            let yfs_disk = YfsDisk::new(EMPTY_BLOCK, inodes, data_blocks);

            let block = yfs_disk.read_block(5).unwrap();
            assert_eq!(block, data_blocks[2]);
        }
    }

    mod write_block {
        use super::*;

        #[test]
        fn test_write_boot_sector() {
            let mut yfs_disk = YfsDisk::new(EMPTY_BLOCK, [FREE_INODE], [EMPTY_BLOCK]);

            let boot_sector = [0xfe; BLOCK_SIZE];
            yfs_disk.write_block(0, &boot_sector).unwrap();
            assert_eq!(yfs_disk.boot_sector, boot_sector);
        }

        #[test]
        fn test_write_out_of_bounds_block() {
            let mut yfs_disk = YfsDisk::new(EMPTY_BLOCK, [FREE_INODE], [EMPTY_BLOCK]);
            assert!(yfs_disk.write_block(2, &EMPTY_BLOCK).is_ok());
            assert!(yfs_disk.write_block(3, &EMPTY_BLOCK).is_err());
            assert!(yfs_disk.write_block(4, &EMPTY_BLOCK).is_err());

            let mut yfs_disk = YfsDisk::new(EMPTY_BLOCK, [FREE_INODE; 7], [EMPTY_BLOCK; 5]);
            assert!(yfs_disk.write_block(6, &EMPTY_BLOCK).is_ok());
            assert!(yfs_disk.write_block(7, &EMPTY_BLOCK).is_err());
            assert!(yfs_disk.write_block(8, &EMPTY_BLOCK).is_err());
        }

        #[test]
        fn test_write_block_one() {
            let mut yfs_disk = YfsDisk::new(EMPTY_BLOCK, [FREE_INODE], [EMPTY_BLOCK]);
            let header = &yfs_disk.file_system_header;

            let mut block = EMPTY_BLOCK;
            block[0..FS_HEADER_SIZE].copy_from_slice(&bincode::serialize(header).unwrap());

            let inode = Inode::new(InodeType::Regular, 3);
            block[FS_HEADER_SIZE..FS_HEADER_SIZE + INODE_SIZE]
                .copy_from_slice(&bincode::serialize(&inode).unwrap());

            yfs_disk.write_block(1, &block).unwrap();

            assert_eq!(yfs_disk.inodes[0], inode);
        }

        #[test]
        fn test_write_inode_block() {
            let mut yfs_disk = YfsDisk::new(EMPTY_BLOCK, [FREE_INODE; 10], [[0xfe; BLOCK_SIZE]]);

            let mut block = EMPTY_BLOCK;
            let inodes = [EMPTY_FILE_INODE, EMPTY_FILE_INODE, EMPTY_FILE_INODE];
            block[..INODE_SIZE * 3].copy_from_slice(&serialize_inodes(&inodes).unwrap());

            yfs_disk.write_block(2, &block).unwrap();

            for (i, inode) in yfs_disk.inodes.into_iter().enumerate() {
                if i < 7 {
                    assert_eq!(inode, FREE_INODE);
                } else {
                    assert_eq!(inode, EMPTY_FILE_INODE);
                }
            }
        }

        #[test]
        fn test_write_data_block() {
            let mut yfs_disk = YfsDisk::new(
                EMPTY_BLOCK,
                [FREE_INODE; 3],
                [EMPTY_BLOCK, EMPTY_BLOCK, EMPTY_BLOCK],
            );

            let block = [0; BLOCK_SIZE];
            yfs_disk.write_block(2, &block).unwrap();
            assert_eq!(yfs_disk.data_blocks[0], block);

            let block = [1; BLOCK_SIZE];
            yfs_disk.write_block(3, &block).unwrap();
            assert_eq!(yfs_disk.data_blocks[1], block);
        }
    }

    const EMPTY_BLOCK: Block = [0; BLOCK_SIZE];

    const EMPTY_FILE_INODE: Inode = Inode {
        type_: InodeType::Regular,
        nlink: 1,
        reuse: 0,
        size: 0,
        direct: [0; NUM_DIRECT],
        indirect: 0,
    };

    const EMPTY_DIRECTORY_INODE: Inode = Inode {
        type_: InodeType::Directory,
        nlink: 1,
        reuse: 0,
        size: 0,
        direct: [0; NUM_DIRECT],
        indirect: 0,
    };
}
