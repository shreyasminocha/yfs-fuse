# YFS FUSE

A FUSE adapter for Yalnix File System (YFS) disks from Rice's OS class.

## Features

- [x] listing directories
- [x] reading files
- [x] writing files
- [x] creating files
- [x] creating directories
- [x] creating hard links
- [x] deleting files
- [x] deleting directories
- [x] renaming files
- [x] symlinks

## Usage

```sh
# cargo run --bin yfs-fuse <disk file> <mount point>
cargo run --bin yfs-fuse DISK /mnt/yfs
```

## Why

FS

## License

[MIT License](./LICENSE)
