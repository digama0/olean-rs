#[macro_use] mod types;
mod deserialize;
mod hasher;
mod args;
mod leanpath;
mod loader;
mod tokens;
mod lexer;
mod rough_parser;
#[allow(dead_code)] mod trie;

use std::io;
use std::fs::File;
use self::args::*;
use self::leanpath::LeanPath;
use self::loader::Loader;
use self::tokens::TokenTable;
use self::rough_parser::RoughParser;

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
        },
        Action::Dependents(name) => {
            let lp = LeanPath::new(&args)?;
            let mut load = Loader::new(lp);
            load.load(name.clone())?;
            for s in load.order { println!("{}", s) }
        },
        Action::Unused(name) => {
            let lp = LeanPath::new(&args)?;
            let mut load = Loader::new(lp);
            load.load(name.clone())?;
            // println!("* order");
            // for s in &load.order { println!("{}", s) }
            println!("* unused imports");
            let x = load.unused_imports(&name);
            for s in x { println!("{}", s) }
        },
        Action::Lex(name) => {
            let lp = LeanPath::new(&args)?;
            let mut load = Loader::new(lp.clone());
            load.load(name.clone())?;
            let n2 = load.order.pop().unwrap();
            let mut table = TokenTable::new();
            table.load(&mut load)?;
            let path = lp.find(n2, "lean").unwrap().1;
            let lex = lexer::from_file(&path, table)?;
            for tk in lex {
                println!("{:?}", tk?)
            }
        },
        Action::Test(name) => {
            let lp = LeanPath::new(&args)?;
            let path = lp.find(name.clone(), "lean").unwrap().1;
            let mut load = Loader::new(lp);
            let lexer = lexer::from_file(&path, TokenTable::new())?;
            let mut rp = RoughParser::new(lexer);
            let rl = rp.parse_lean(&mut load, name.clone())?;
            for tk in rl.cmds { println!("{}", tk) }
        },
        Action::None => args.print_usage_and_exit(1)
    }
    Ok(())
}
