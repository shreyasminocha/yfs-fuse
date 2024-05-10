#![feature(array_chunks)]
#![feature(int_roundings)]
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

//! An implementation of the YFS disk format, YFS operations, and a FUSE wrapper around YFS.

/// Constants and structures that define the YFS disk format.
mod disk_format;
/// An implementation of a FUSE filesystem around YFS.
pub mod fuse;
/// Filesystem metadata structures.
mod metadata;
/// Implementations of storage backends that support YFS-style block-based I/O.
pub mod storage;
/// Implementations of YFS operations.
pub mod yfs;
