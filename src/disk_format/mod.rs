/// Perform a const assertion.
macro_rules! const_assert {
    ($($tt:tt)*) => {
        const _: () = assert!($($tt)*);
    }
}

/// YFS blocks.
pub mod block;
/// The YFS boot sector/block.
pub mod boot_sector;
/// Directory entries and entry names.
pub mod directory_entry;
/// The filesystem header.
pub mod header;
/// Inodes.
pub mod inode;
