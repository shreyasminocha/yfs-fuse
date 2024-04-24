# YFS FUSE

A FUSE adapter for Yalnix File System (YFS) disks from Rice's OS class.

Note: the code is currently poorly documented and missing tests.

## Features

- [x] listing directories
- [x] reading files
- [ ] creating files
- [ ] deleting files
- [x] writing files (buggy)
- [ ] symlinks
- [ ] …

## Usage

```sh
# cargo run <disk file> <mount point>
cargo run DISK /mnt/yfs
```

## Why

FS

## License

[MIT License](./LICENSE)
