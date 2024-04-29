//! Constants and structures that define the YFS disk format.

macro_rules! const_assert {
    ($($tt:tt)*) => {
        const _: () = assert!($($tt)*);
    }
}

pub mod block;
pub mod boot_sector;
pub mod directory_entry;
pub mod header;
pub mod inode;
