use std::time::SystemTime;

/// The time metadata associated with files in most filesystems (not including YFS).
pub struct TimeMetadata {
    /// Last access time.
    pub atime: SystemTime,
    /// Last modification time.
    pub mtime: SystemTime,
    /// Creation time.
    pub crtime: SystemTime,
}

impl Default for TimeMetadata {
    fn default() -> Self {
        Self {
            atime: SystemTime::UNIX_EPOCH,
            mtime: SystemTime::UNIX_EPOCH,
            crtime: SystemTime::UNIX_EPOCH,
        }
    }
}

/// The time metadata associated with files in most filesystems (not including YFS).
#[derive(Default)]
pub struct OwnershipMetadata {
    /// Owner user ID.
    pub uid: u32,
    /// Owner group ID.
    pub gid: u32,
}
