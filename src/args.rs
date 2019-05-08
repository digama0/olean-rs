use std::io;
use std::env;
use std::process::Command;
use std::path::{Path, PathBuf};
use std::ffi::OsStr;
use getopts::Options;
use std::process::exit;
use crate::types;

fn find_it<P>(exe_name: P) -> Option<PathBuf>
    where P: AsRef<Path> {
    env::var_os("PATH").and_then(|paths| {
        env::split_paths(&paths).filter_map(|dir| {
            let mut full_path = dir.join(&exe_name);
            if cfg!(windows) {
                full_path.set_extension("exe");
            }
            if full_path.is_file() {
                Some(full_path)
            } else {
                None
            }
        }).next()
    })
}

fn elan_find_it<P>(exe_name: P) -> Option<PathBuf>
    where P: AsRef<OsStr> {
    Command::new("elan")
        .arg("which")
        .arg(exe_name)
        .output()
        .ok()
        .map(|r| PathBuf::from(String::from_utf8(r.stdout).expect("bad string")))
}

pub enum Action {
    Dump(PathBuf),
    Dependents(PathBuf),
    // Lint(PathBuf),
    Unused(PathBuf),
    Clique(PathBuf),
    Makefile,
    // Lex(types::Name),
    Test(types::Name),
    None
}

pub struct Args {
    pub act: Action,
    program: String,
    opts: Options,
    library: Option<PathBuf>
}

impl Args {
    pub fn new() -> Args {
        let args: Vec<String> = env::args().collect();
        let opts = Options::new();

        Args {
            act: Action::None,
            program: args[0].clone(),
            opts, library: None }
    }

    pub fn print_usage_and_exit(&self, code: i32) -> ! {
        let brief = format!("Usage: {} [options]", self.program);
        print!("{}", self.opts.usage(&brief));
        exit(code)
    }

    pub fn lean_path() -> Option<PathBuf> {
        elan_find_it("lean").and_then(|p| Some(p.parent()?.parent()?.to_path_buf()))
            .or_else(|| Some(find_it("lean")?.parent()?.parent()?.to_path_buf())) }

    pub fn library(&self) -> Option<PathBuf> {
        self.library.clone()
            .or_else(||  Args::lean_path())
    }
}

pub fn args() -> io::Result<Args> {
    let args: Vec<String> = env::args().collect();

    let mut opts = Options::new();
    opts.optopt("D", "dump", "dump olean parse", "FILE");
    opts.optopt("d", "deps", "view all dependents of the target file", "FILE");
    opts.optopt("u", "unused", "list unused imports", "FILE");
    opts.optflag("m", "makefile", "generate a makefile to build and check project");
    opts.optopt("l", "lint",     "check file for various ", "FILE");
    opts.optopt("c", "clique", "find sets of declarations that depend on separate sets of imports", "FILE");
    opts.optflag("L", "", "give location of lean library");
    opts.optopt("p", "", "set current working directory", "DIR");
    // opts.optopt("l", "", "test lexer", "lean.name");
    opts.optopt("t", "", "testing", "lean.name");
    opts.optflag("h", "help", "print this help menu");
    let matches = opts.parse(&args[1..]).unwrap();
    let mut args = Args {
        act: Action::None,
        program: args[0].clone(),
        opts, library: None };
    if matches.opt_present("h") { args.print_usage_and_exit(0) }
    if let Some(s) = matches.opt_str("p") { env::set_current_dir(&s)? }
    if let Some(s) = matches.opt_str("D") {
        args.act = Action::Dump(PathBuf::from(s))
    }
    if let Some(s) = matches.opt_str("L") {
        args.library = Some(PathBuf::from(s))
    }
    if let Some(s) = matches.opt_str("d") {
        args.act = Action::Dependents(PathBuf::from(s))
        // args.act = Action::Dependents(types::parse_name(&s))
    }
    // if let Some(s) = matches.opt_str("l") {
    //     args.act = Action::Lex(types::parse_name(&s))
    // }
    if let Some(s) = matches.opt_str("t") {
        args.act = Action::Test(types::parse_name(&s))
    }
    if let Some(s) = matches.opt_str("u") {
        // args.act = Action::Unused(types::parse_name(&s))
        args.act = Action::Unused(PathBuf::from(s))
    }
    // if let Some(s) = matches.opt_str("l") {
    //     // args.act = Action::Unused(types::parse_name(&s))
    //     args.act = Action::Lint(PathBuf::from(s))
    // }
    if let Some(s) = matches.opt_str("c") {
        // args.act = Action::Unused(types::parse_name(&s))
        args.act = Action::Clique(PathBuf::from(s))
    }
    if matches.opt_present("m") {
        args.act = Action::Makefile
    }
    if matches.opt_present("h") {
        args.print_usage_and_exit(0)
    }
    Ok(args)
}
