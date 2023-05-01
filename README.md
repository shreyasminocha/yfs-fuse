# YFS FUSE

A FUSE adapter for Yalnix File System (YFS) disks from Rice's OS class.

Note: the code is currently messy and brittle.

## Features

- [x] listing directories
- [x] reading files
- [ ] creating files
- [ ] deleting files
- [ ] writing files
- [ ] symlinks
- [ ] …

## Usage

```
# cargo run <disk file> <mount point>
cargo run DISK /mnt/yfs
```

## Why

FS

## License

[MIT License](./LICENSE)
