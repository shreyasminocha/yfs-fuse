#![feature(array_chunks)]
#![feature(int_roundings)]
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]
#![warn(clippy::explicit_iter_loop)]
#![warn(clippy::items_after_statements)]
#![warn(clippy::large_types_passed_by_value)]
#![warn(clippy::must_use_candidate)]
#![warn(clippy::needless_pass_by_value)]
#![warn(clippy::redundant_closure_for_method_calls)]
#![warn(clippy::similar_names)]

//! An implementation of the YFS disk format, YFS operations, and a FUSE wrapper around YFS.

/// Constants and structures that define the YFS disk format.
mod disk_format;
/// An implementation of a FUSE filesystem around YFS.
pub mod fs;
/// Implementations of storage backends that support YFS-style block-based I/O.
pub mod storage;
/// Implementations of YFS operations.
pub mod yfs;
