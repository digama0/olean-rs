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
        Action::Lex(name) => {
            let lp = LeanPath::new(&args)?;
            let mut load = Loader::load(&lp, name.clone())?;
            let n2 = load.order.pop().unwrap();
            let table = tokens::token_table(&mut load)?;
            let path = lp.find(n2, "lean").unwrap().1;
            let lex = lexer::from_file(&path, table)?;
            for tk in lex {
                println!("{:?}", tk?)
            }
            Ok(()) },
        Action::Test(name) => {
            let lp = LeanPath::new(&args)?;
            let table = tokens::TokenTable::new();
            let path = lp.find(name.clone(), "lean").unwrap().1;
            let lex = lexer::from_file(&path, table)?;
            let mut parser = rough_parser::RoughParser::new(lex)?;
            let rl = parser.parse()?;
            println!("{:?}", rl);
            Ok(()) },
        Action::None => args.print_usage_and_exit(1)
    }
}
