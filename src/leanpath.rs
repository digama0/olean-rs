use std::io;
use std::io::{BufRead, BufReader};
use std::env;
use std::path::{Path, PathBuf};
use std::fs::File;
use crate::args;
use crate::types::{Name, Name2};

fn get_leanpkg_path_file() -> Option<PathBuf> {
    let mut path: &Path = &env::current_dir().ok()?;
    loop {
        let mut path2: PathBuf = path.to_path_buf();
        path2.push("leanpkg.path");
        if path2.exists() { return Some(path2) }
        path = path.parent()?
    }
}

pub struct LeanPath(pub Vec<PathBuf>);

fn name_to_path(n: &Name2) -> Option<PathBuf> {
    match n {
        Name2::Anon => Some(PathBuf::new()),
        Name2::Str(ref n, ref s) => name_to_path(n).map(|mut p| {p.push(s.clone()); p}),
        Name2::Num{..} => None
    }
}

impl LeanPath {

    pub fn new(args: &args::Args) -> io::Result<LeanPath> {
        let path = get_leanpkg_path_file().unwrap_or_else(||
            panic!("can't find leanpkg.path; make sure you are in a lean project"));
        let mut res = Vec::new();
        for l in BufReader::new(File::open(&path)?).lines() {
            let l = l?;
            if l.starts_with("path ") {
                res.push(path.parent().unwrap().join(&l[5..]));
            } else if l == "builtin_path" {
                let lib = args.library().unwrap_or_else(||
                    panic!("can't find lean; use the -L switch to say where the lean root is"));
                let mut lib1 = lib.clone(); lib1.push("library"); res.push(lib1);
                let mut lib2 = lib.clone(); lib2.push("lib"); lib2.push("lean"); lib2.push("library"); res.push(lib2);
            }
        }
        Ok(LeanPath(res))
    }

    pub fn find_path(&self, p: &Path) -> Option<PathBuf> {
        for ref dir in &self.0 {
            let f = dir.join(p);
            if f.exists() { return Some(f) }
        }
        None
    }

    pub fn find_inner(&self, n: Name, ext: &str) -> Option<(Name, PathBuf)> {
        self.find_path(&name_to_path(&n)?.with_extension(ext)).map(|p| (n, p))
    }

    pub fn find(&self, n: Name, ext: &str) -> Option<(Name, PathBuf)> {
        self.find_inner(n.clone(), ext).or_else(||
            self.find_inner(name![n; default], ext))
    }
}
