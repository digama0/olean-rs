mod deserialize;
mod types;
mod hasher;

use std::io;
use std::fs::File;
use std::env;

#[macro_use] extern crate num_derive;

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() <= 1 {
        println!("use: {} path/to/file.olean", args[0]);
    } else {
        let ol = deserialize::read_olean(File::open(&args[1])?)?;
        println!("{}", ol);
        println!("===================");
        let mods = deserialize::read_olean_modifications(&ol.code)?;
        for m in mods {
            println!("{:?}", m);
        }
    }
    Ok(())
}
