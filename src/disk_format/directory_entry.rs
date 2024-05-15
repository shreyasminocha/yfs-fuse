use std::{
    ffi::{CStr, CString},
    fmt::{self, Debug},
    mem::size_of,
};

use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};

use super::block::BLOCK_SIZE;

/// The number of bytes occupied by a directory entry.
pub const DIRECTORY_ENTRY_SIZE: usize = 32;
const_assert!(size_of::<DirectoryEntry>() == DIRECTORY_ENTRY_SIZE);

const_assert!(BLOCK_SIZE % DIRECTORY_ENTRY_SIZE == 0);
/// The number of directory entries that fit in a block.
pub const DIRECTORY_ENTRIES_PER_BLOCK: usize = BLOCK_SIZE / DIRECTORY_ENTRY_SIZE;

/// The maximum supported size of a file or directory name, excluding the nul-terminator.
pub const MAX_NAME_LEN: usize = 30;
const_assert!(size_of::<DirectoryEntryName>() == MAX_NAME_LEN);

/// A free directory entry.
pub const FREE_DIRECTORY_ENTRY: DirectoryEntry = DirectoryEntry {
    inum: 0,
    name: DirectoryEntryName([0; 30]),
};

/// A directory entry.
#[derive(Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(C)]
pub struct DirectoryEntry {
    /// The inode number.
    pub inum: i16,
    /// The name of the entry.
    pub name: DirectoryEntryName,
}

impl DirectoryEntry {
    /// Constructs a new [`DirectoryEntry`] instance.
    pub fn new(inum: i16, name: &CStr) -> Result<DirectoryEntry> {
        Ok(DirectoryEntry {
            inum,
            name: name.try_into()?,
        })
    }
}

/// A name, as used in [`DirectoryEntry`].
///
/// A maximum of 30-byte-long names are supported.
#[derive(Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(C)]
pub struct DirectoryEntryName([u8; 30]);

impl Debug for DirectoryEntryName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("DirectoryEntryName")
            .field(&CString::from(self))
            .finish()
    }
}

impl TryFrom<&CStr> for DirectoryEntryName {
    type Error = anyhow::Error;

    fn try_from(value: &CStr) -> Result<Self, Self::Error> {
        ensure!(
            value.count_bytes() <= 30,
            "string is more than 30 characters long"
        );

        let bytes = value.to_bytes();
        let mut converted = [0; 30];
        converted[0..bytes.len()].copy_from_slice(bytes);

        Ok(DirectoryEntryName(converted))
    }
}

impl From<&DirectoryEntryName> for CString {
    fn from(val: &DirectoryEntryName) -> Self {
        let mut bytes = val.0.to_vec();
        bytes.push(0); // add a nul byte in case there are none

        CString::from(CStr::from_bytes_until_nul(&bytes).expect("we suffixed a nul byte"))
    }
}

impl fmt::Display for DirectoryEntryName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let cstr = CString::from(self);
        let Ok(string) = cstr.into_string() else {
            return Err(fmt::Error);
        };

        write!(f, "{string}")
    }
}
