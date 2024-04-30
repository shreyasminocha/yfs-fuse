use std::{
    ffi::{CStr, CString},
    fmt,
    mem::size_of,
};

use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};

use super::block::BLOCK_SIZE;

pub const DIRECTORY_ENTRY_SIZE: usize = 32;
const_assert!(size_of::<DirectoryEntry>() == DIRECTORY_ENTRY_SIZE);

const_assert!(BLOCK_SIZE % DIRECTORY_ENTRY_SIZE == 0);
pub const DIRECTORY_ENTRIES_PER_BLOCK: usize = BLOCK_SIZE / DIRECTORY_ENTRY_SIZE;

pub const FREE_DIRECTORY_ENTRY: DirectoryEntry = DirectoryEntry {
    inum: 0,
    name: DirectoryName([0; 30]),
};

#[derive(Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct DirectoryEntry {
    /// inode number
    pub inum: i16,
    /// file name (not null-terminated)
    pub name: DirectoryName,
}

impl DirectoryEntry {
    pub fn new(inum: i16, name: &CStr) -> Result<DirectoryEntry> {
        Ok(DirectoryEntry {
            inum,
            name: name.try_into()?,
        })
    }
}

#[derive(Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DirectoryName([u8; 30]);

impl TryFrom<&CStr> for DirectoryName {
    type Error = anyhow::Error;

    fn try_from(value: &CStr) -> Result<Self, Self::Error> {
        if value.count_bytes() > 30 {
            bail!("string is more than 30 characters long")
        }

        let bytes = value.to_bytes();
        let mut converted = [0; 30];
        converted[0..bytes.len()].copy_from_slice(bytes);

        Ok(DirectoryName(converted))
    }
}

impl From<&DirectoryName> for CString {
    fn from(val: &DirectoryName) -> Self {
        let mut bytes = val.0.to_vec();
        bytes.push(0); // add a nul byte in case there are none

        CString::from(CStr::from_bytes_until_nul(&bytes).expect("we suffixed a nul byte"))
    }
}

impl fmt::Display for DirectoryName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let cstr = CString::from(self);
        let Ok(string) = cstr.into_string() else {
            return Err(fmt::Error);
        };

        write!(f, "{string}")
    }
}
