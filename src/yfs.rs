use serde::Deserialize;

const INODE_SIZE: usize = 64;
const NUM_DIRECT: usize = 12;

type InodeNumber = i16;

#[derive(Deserialize)]
struct DirectoryEntry {
    /// inode number
    inum: InodeNumber,
    /// file name (not null-terminated)
    name: [u8; 30],
}

#[derive(Deserialize)]
struct Inode {
    /// file type (e.g., directory or regular)
    type_: FileType,
    /// number of hard links to inode
    nlink: i16,
    /// inode reuse count
    reuse: i32,
    /// file size in bytes
    size: i32,
    /// block #s for 1st NUM_DIRECT blocks
    direct: [i32; NUM_DIRECT],
    /// block number of indirect block
    indirect: i32,
}

#[derive(Deserialize)]
#[repr(i16)]
enum FileType {
    /// This inode is not in use for any file.
    Free = 0,
    /// This inode describes a directory.
    Directory = 1,
    /// This inode describes a regular data file.
    Regular = 2,
    /// This inode describes a symbolic link.
    Symlink = 3,
}
