use fuser::{Filesystem, ReplyAttr, ReplyData, ReplyDirectory, ReplyEntry, Request};
use std::ffi::OsStr;
use std::fs::File;

pub struct Yfs(pub File);

impl Filesystem for Yfs {
    fn lookup(&mut self, _req: &Request, parent: u64, name: &OsStr, reply: ReplyEntry) {
        todo!()
    }

    fn getattr(&mut self, _req: &Request, ino: u64, reply: ReplyAttr) {
        todo!()
    }

    fn read(
        &mut self,
        _req: &Request,
        ino: u64,
        _fh: u64,
        offset: i64,
        size: u32,
        _flags: i32,
        _lock: Option<u64>,
        reply: ReplyData,
    ) {
        todo!()
    }

    fn readdir(
        &mut self,
        _req: &Request,
        ino: u64,
        _fh: u64,
        offset: i64,
        mut reply: ReplyDirectory,
    ) {
        todo!()
    }
}
