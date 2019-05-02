use std::path::*;
use std::io;
use std::fs::File;
// use serde::{Serialize, Deserialize};

use crate::leanpath::*;
use crate::loader::*;
use crate::types::*;

extern crate serde_yaml;

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct LeantConfig {
    pub unused_imports : bool,
    pub doc_string_for_types : bool,
    pub doc_string_for_defs : bool,
    pub doc_string_for_user_tactics : bool,
    // pub doc_string_for_lemma : bool,
    pub doc_string_for_theorem : bool,
    pub doc_string_for_classes : bool,
    // pub redundant_instances_in_thm : bool
}

impl LeantConfig {
    #[allow(dead_code)]
    pub const DEFAULT : LeantConfig =
        LeantConfig { unused_imports : true,
                      doc_string_for_types : true,
                      doc_string_for_defs : false,
                      doc_string_for_user_tactics : false,
                      doc_string_for_classes : false,
                      doc_string_for_theorem : false,
                      // redundant_instances_in_thm : false
        };

    #[allow(dead_code)]
    pub fn write_config(cfg : &LeantConfig) -> io::Result<()> {
        let fp = File::create("leant.yaml")?;
        serde_yaml::to_writer(fp, cfg).map_err(|err| {
            io::Error::new(io::ErrorKind::InvalidData, format!("parsing error: {}", err)) }) }

    #[allow(dead_code)]
    pub fn read_config() -> io::Result<LeantConfig> {
        File::open("leant.yaml")
            .and_then(|fp| {
                serde_yaml::from_reader(fp).map_err(|err| {
                    io::Error::new(io::ErrorKind::InvalidData, format!("parsing error: {}", err)) }) })
            .or_else(|_| {
                let fp = File::create("leant.yaml")?;
                let cfg = LeantConfig::DEFAULT;
                serde_yaml::to_writer(fp, &cfg).map_err(|err| {
                    io::Error::new(io::ErrorKind::InvalidData, format!("parsing error: {}", err)) })?;
                Result::Ok( cfg )
            } ) }
}

// fn run(checkers : &[(bool, Box<FnOnce() -> io::Result<bool>>)]) -> io::Result<bool> {
//     let mut res = false;
//     for (b,cmd) in checkers {
//         if *b { res = res || (*cmd)()?; }
//     }
//     Result::Ok( res )
// }

#[allow(dead_code)]
pub fn run_checkers(file : &PathBuf, lp : LeanPath) -> io::Result<()> {
    let opt : LeantConfig = LeantConfig::read_config()?;
    let name = path_to_name(&lp, file.as_path())
        .expect(format!("cannot resolve path: {:?}", file).as_str());
    let mut load = Loader::new(lp);
    load.load(name.clone())?;
    let r = opt.unused_imports && check_unused_imports(&name, &mut load)? ||
        check_doc_strings(&name, &mut load, &opt);
    if r { ::std::process::exit(-1) }
    Ok( () )
}

pub fn check_unused_imports(name : &Name, load : &mut Loader) -> io::Result<bool> {
    // let opt : LeantConfig = read_config()?;
    load.load(name.clone())?;
    // println!("* order");
    // for s in &load.order { println!("{}", s) }
    let x = load.unused_imports(&name);
    if !x.is_empty() {
        println!("\n\n* unused imports for {:?}", name);
        for s in &x {
            println!("{}",  s) };
        println!("\n"); }
    Result::Ok(!x.is_empty())
}

    // pub doc_string_for_types : bool,
    // pub doc_string_for_classes : bool,
    // pub doc_string_for_defs : bool,
    // pub doc_string_for_user_tactics : bool,
    // pub doc_string_for_lemma : bool,
    // pub doc_string_for_theorem : bool,

#[allow(dead_code)]
pub fn check_doc_strings(name : &Name, load : &mut Loader, cfg : &LeantConfig) -> bool {
    use Symbol::*;
    // println!("load interace");
    let m = load.get_interface(name);
    let mut r : bool = false;
    // println!("end (load interace)\n - {:?}\n - {:?}", m, cfg);
    for (n,y) in m.iter() {
        // println!("- {:?}, doc string: {}, type: {:?}", n, y.2, y.0);
        let b = y.2 || y.1 == Visibility::Private ||
            match y.0 {
                Type => !cfg.doc_string_for_types,
                Def => !cfg.doc_string_for_defs,
                UserTactic => !cfg.doc_string_for_user_tactics,
                Theorem => !cfg.doc_string_for_theorem,
                Class => !cfg.doc_string_for_classes
            };
        if !b { println!("{} {} should have a doc string\n", y.0, n); }
        r = b || r }
    r
}
