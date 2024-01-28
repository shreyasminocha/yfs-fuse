use anyhow::{Context, Result};
use clap::Parser;
use std::fs::File;
use std::path::PathBuf;

use yfs::fuse::Yfs;
use yfs::yfs::YfsDisk;

#[derive(Parser)]
struct Args {
    /// YFS disk file
    disk_file: PathBuf,
    /// FUSE mountpoint
    mountpoint: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let disk_file_path = args.disk_file;
    let disk_file = File::options()
        .read(true)
        .write(true)
        .open(disk_file_path)
        .context("unable to open disk file in read-write mode")?;

    let yfs = YfsDisk::from_file(disk_file)?;

    let mountpoint = args.mountpoint;
    fuser::mount2(Yfs(yfs), mountpoint, &[]).unwrap();

    Ok(())
}
