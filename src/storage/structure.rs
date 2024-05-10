use anyhow::{bail, Context, Result};

use crate::{
    disk_format::{
        block::{Block, BLOCK_SIZE},
        header::FileSystemHeader,
        inode::{Inode, INODES_PER_BLOCK},
    },
    yfs::BlockNumber,
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
}

impl<const I: usize, const D: usize> YfsStorage for YfsDisk<I, D> {
    fn read_block(&self, block_number: BlockNumber) -> Result<Block> {
        let block = match block_number {
            0 => self.boot_sector,
            1 => {
                let header_serialized = bincode::serialize(&self.file_system_header)?;

                let inodes = &self.inodes[0..(INODES_PER_BLOCK - 1).min(I)];
                let inodes_serialized = serialize_inodes(inodes)?;

                let mut block = [header_serialized, inodes_serialized].concat();
                block.resize(BLOCK_SIZE, 0);

                block
                    .try_into()
                    .expect("we resized the vector to BLOCK_SIZE")
            }
            ib if ib >= 2 && ib <= Self::NUM_INODE_BLOCKS => {
                let inode_range_start = ((ib - 1) * INODES_PER_BLOCK) - 1;
                let inode_range_end = ((ib * INODES_PER_BLOCK) - 1).min(I);
                let inodes = &self.inodes[inode_range_start..inode_range_end];

                let mut block = serialize_inodes(inodes)?;
                block.resize(BLOCK_SIZE, 0);

                block
                    .try_into()
                    .expect("we resized the vector to BLOCK_SIZE")
            }
            db if db > Self::NUM_INODE_BLOCKS && db < Self::NUM_BLOCKS => {
                self.data_blocks[db - Self::NUM_INODE_BLOCKS - 1]
            }
            _ => bail!("block number out of bounds"),
        };

        Ok(block)
    }

    fn write_block(&self, _block_number: BlockNumber, _block: &Block) -> Result<()> {
        todo!("implement block writing")
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
            } else {
                assert_eq!(inode.type_, InodeType::Free);
                assert_eq!(inode.direct, [0; NUM_DIRECT]);
                assert_eq!(inode.indirect, 0);
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
