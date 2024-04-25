use std::fs::File;
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Parser;

use yfs::fuse::YfsFs;
use yfs::yfs::Yfs;

#[derive(Parser)]
struct Args {
    /// YFS disk file
    disk_file: PathBuf,
    /// FUSE mountpoint
    mountpoint: PathBuf,
}

fn main() -> Result<()> {
    env_logger::init();

    let args = Args::parse();

    let disk_file_path = args.disk_file;
    let disk_file = File::options()
        .read(true)
        .write(true)
        .open(disk_file_path)
        .context("unable to open disk file in read-write mode")?;

    let yfs = Yfs::from_file(disk_file)?;

    let mountpoint = args.mountpoint;
    fuser::mount2(YfsFs::new(yfs)?, mountpoint, &[]).unwrap();

    Ok(())
}
