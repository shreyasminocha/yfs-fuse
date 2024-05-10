# YFS FUSE

A FUSE adapter for Yalnix File System (YFS) disks from Rice's OS class.

> [!NOTE]
> The code currently lacks tests.

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
# cargo run <disk file> <mount point>
cargo run DISK /mnt/yfs
```

## Why

FS

## License

[MIT License](./LICENSE)
