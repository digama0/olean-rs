mod deserialize;
mod types;
mod hasher;
mod args;
mod leanpath;
mod loader;

use std::io;
use std::fs::File;
use self::args::*;
use self::leanpath::LeanPath;
use self::loader::Loader;

#[macro_use] extern crate num_derive;
extern crate getopts;

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
            Ok(())
        }
        Action::Dependents(name) => {
            let start = types::parse_name(&name);
            let lp = LeanPath::new(&args)?;
            let Loader{map:_, order} = Loader::load(&lp, start)?;
            for s in order { println!("{}", s) }
            Ok(())
        }
        Action::None => args.print_usage_and_exit(1)
    }
}
