use clap::{crate_version, Arg, Command};
use std::fs::File;

use yfs::fuse::Yfs;

fn main() {
    let matches = Command::new("yfs")
        .version(crate_version!())
        .arg(
            Arg::new("DISK_FILE")
                .required(true)
                .index(1)
                .help("YFS disk file"),
        )
        .arg(
            Arg::new("MOUNT_POINT")
                .required(true)
                .index(2)
                .help("FUSE mountpoint"),
        )
        .get_matches();

    let disk_file_path = matches.value_of("DISK_FILE").unwrap();
    let disk_file = File::open(disk_file_path).expect("unable to open disk file");

    let mountpoint = matches.value_of("MOUNT_POINT").unwrap();

    todo!();

    fuser::mount2(Yfs(disk_file), mountpoint, &[]).unwrap();
}
