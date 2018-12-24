mod deserialize;
mod types;
mod hasher;
mod args;
mod leanpath;
mod loader;
mod scanner;
// mod flet;
#[allow(dead_code)] mod trie;

use std::io;
use std::fs::File;
use self::args::*;
use self::leanpath::LeanPath;
use self::loader::Loader;

#[macro_use] extern crate num_derive;
extern crate getopts;
extern crate endian_type;
extern crate nibble_vec;

fn main() -> io::Result<()> {
    let args = args()?;
    match &args.act {
        Action::Dump(file) => {
            let ol = deserialize::read_olean(File::open(&file)?)?;
            println!("{}", ol);
            println!("===================");
            let mods = deserialize::read_olean_modifications(&ol.code)?;
            for m in mods {
                println!("{:?}", m);
            }
            Ok(()) },
        Action::Dependents(name) => {
            let lp = LeanPath::new(&args)?;
            let Loader{map:_, order} = Loader::load(&lp, name.clone())?;
            for s in order { println!("{}", s) }
            Ok(()) },
        Action::Scan(name) => {
            let lp = LeanPath::new(&args)?;
            let mut load = Loader::load(&lp, name.clone())?;
            let n2 = load.order.pop().unwrap();
            let table = scanner::get_token_table(&mut load)?;
            let path = lp.find(n2, "lean").unwrap().1;
            let scan = scanner::from_file(&path, table)?;
            for tk in scan {
                println!("{:?}", tk);
            }
            Ok(()) },
        Action::Test(name) => {
            let lp = LeanPath::new(&args)?;
            let mut load = Loader::load(&lp, name.clone())?;
            let table = scanner::get_token_table(&mut load)?;
            for tk in &table {
                println!("{:?}", tk);
            }
            Ok(()) },
        Action::None => args.print_usage_and_exit(1)
    }
}
