# YFS FUSE

A FUSE adapter for Yalnix File System (YFS) disks from Rice's OS class.

Note: the code is currently poorly documented and missing tests.

## Features

- [x] listing directories
- [x] reading files
- [x] writing files
- [x] creating files
- [ ] creating directories
- [ ] deleting files
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
