use std::{fs::File, path::PathBuf};

use anyhow::Result;
use clap::Parser;
use yfs::{storage::FileBackedStorage, yfs::Yfs};

#[derive(Parser)]
struct Args {
    /// YFS disk file
    disk_file: PathBuf,
}

fn main() -> Result<()> {
    env_logger::init();

    let args = Args::parse();

    let disk_file = File::options().read(true).open(args.disk_file)?;
    let storage = FileBackedStorage::new(disk_file);

    let _ = Yfs::new(storage)?;

    Ok(())
}
