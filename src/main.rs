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
use std::io::prelude::*;
use std::ffi::{OsString};

use self::args::*;
use self::leanpath::LeanPath;
use self::loader::Loader;
use self::tokens::TokenTable;
use self::rough_parser::RoughParser;
use walkdir::WalkDir;
// use crate::leanpath;

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
        Action::Dependents(file) => {
            let lp = LeanPath::new(&args)?;
            let name = leanpath::path_to_name(&lp, file.as_path()).expect(format!("cannot resolve path: {:?}", file).as_str());
            let mut load = Loader::new(lp);
            load.load(name.clone())?;
            for s in load.order { println!("{}", s) }
        },
        Action::Unused(file) => {
            let lp = LeanPath::new(&args)?;
            let name = leanpath::path_to_name(&lp, file.as_path()).expect(format!("cannot resolve path: {:?}", file).as_str());
            // lp.find(name, "olean");
            let mut load = Loader::new(lp);
            load.load(name.clone())?;
            // println!("* order");
            // for s in &load.order { println!("{}", s) }
            let x = load.unused_imports(&name);
            if !x.is_empty() {
                println!("\n\n* unused imports for {:?}", name);
                for s in &x {
                    let xs : Vec<String> = s.iter().map(|x| format!("{:?}", x)).collect();
                    println!("{}",  xs.join(", ")) };
                println!("\n");
                ::std::process::exit(-1) }
        },
        Action::Makefile => {
            use leanpath::path_to_name_inner;
            let lp = LeanPath::new(&args)?;
            let mut load = Loader::new(lp.clone());
            let mut file = File::create("Makefile")?;
            file.write( "%.olean: %.lean\n".as_bytes() )?;
            file.write( "\tlean --make $<\n".as_bytes() )?;
            file.write( "\tolean-rs -u $@\n\n".as_bytes() )?;
            let mut src = Vec::new();
            for (dir,builtin) in lp.0.clone() {
                let dir = dir.as_path();
                if !builtin {
                    for fp in WalkDir::new(dir).into_iter().filter_map(|e| e.ok()) {
                        let emp = OsString::from("");
                        let path = fp.path();
                        if path.is_file() && path.extension().unwrap_or(emp.as_os_str()) == "olean" {
                            let rel_path = leanpath::make_relative(dir, path).expect(format!("{:?} should be included in {:?}", path, dir).as_str()).with_extension("olean");
                            let n = path_to_name_inner(rel_path.as_path());
                            load.load(n.clone())?;
                            let mut deps : Vec<String> = Vec::new();
                            for imp in &load.map.get(&n).expect(format!("{:?} not found", n).as_str()).0.imports {
                                if let Some(x) = lp.find(imp.resolve(n.clone()), "olean")
                                    .and_then(|p| lp.make_local(p.1.as_path())) {
                                        deps.push(String::from(x.to_string_lossy())) } }
                            let path_str : String = String::from(rel_path.to_string_lossy());
                            src.push(path_str.clone());
                            let out = format!("{}: {}\n", path_str, deps.join(" "));
                            file.write(out.as_bytes())?; } } } }
            file.write(format!("all: {}", src.join(" ")).as_bytes())?;
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
