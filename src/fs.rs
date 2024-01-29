use std::time::SystemTime;

pub struct TimeMetadata {
    pub atime: SystemTime,
    pub mtime: SystemTime,
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

#[derive(Default)]
pub struct OwnershipMetadata {
    pub uid: u32,
    pub gid: u32,
}
