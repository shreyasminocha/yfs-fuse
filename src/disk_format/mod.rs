/// Perform a const assertion.
macro_rules! const_assert {
    ($($tt:tt)*) => {
        const _: () = assert!($($tt)*);
    }
}

/// YFS blocks.
pub(crate) mod block;
/// The YFS boot sector/block.
pub(crate) mod boot_sector;
/// Directory entries and entry names.
pub(crate) mod directory_entry;
/// The filesystem header.
pub(crate) mod header;
/// Inodes.
pub(crate) mod inode;
