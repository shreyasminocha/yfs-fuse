use std::fs::File;
use std::path::PathBuf;

use anyhow::Result;
use clap::Parser;

use fuser::MountOption;
use yfs::fs::YfsFs;
use yfs::storage::FileBackedStorage;
use yfs::yfs::Yfs;

#[derive(Parser)]
struct Args {
    /// YFS disk file
    disk_file: PathBuf,
    /// FUSE mountpoint
    mountpoint: PathBuf,
    /// Mount filesystem as read-only
    #[arg(long, default_value_t = false)]
    read_only: bool,
}

fn main() -> Result<()> {
    env_logger::init();

    let args = Args::parse();

    let disk_file = File::options()
        .read(true)
        .write(!args.read_only)
        .open(args.disk_file)?;

    let yfs = Yfs::new(FileBackedStorage::new(disk_file))?;

    fuser::mount2(
        YfsFs::new(yfs)?,
        args.mountpoint,
        &[
            MountOption::AllowRoot,
            MountOption::AutoUnmount,
            if args.read_only {
                MountOption::RO
            } else {
                MountOption::RW
            },
        ],
    )?;

    Ok(())
}
