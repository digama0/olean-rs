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

#[derive(Clone,Debug)]
pub enum DirScope {
    Project, Library }

#[derive(Clone)]
pub struct LeanPath(pub Vec<(PathBuf,DirScope)>);

pub fn name_to_path(n: &Name2) -> Option<PathBuf> {
    match n {
        Name2::Anon => Some(PathBuf::new()),
        Name2::Str(ref n, ref s) => name_to_path(n).map(|mut p| {p.push(s.clone()); p}),
        Name2::Num{..} => None
    }
}

pub fn path_to_name_inner(n: &Path) -> Name {
    if let Some (fp) = n.file_stem() {
        path_to_name_inner(n.parent().expect("bad path")).str(fp.to_str().expect("invalid string").to_string())
    } else { Name::anon() } }

pub fn path_to_name(lp : &LeanPath, n: &Path) -> Option<Name> {
    Some (path_to_name_inner(lp.make_relative(n.canonicalize().expect(format!("path not found: {:?}", n).as_str()).as_path())?.as_path()))
}

pub fn make_relative(dir : &Path, fp : &Path) -> Option<PathBuf> {
    let mut it0 = dir.components();
    let mut it1 = fp.components();
    let it2 = (&mut it0).zip(&mut it1).take_while(|x| x.0 == x.1);
    for _x in it2 { }
    if let Some(_) = it0.next() {
        None
    } else {
        Some(it1.as_path().to_path_buf()) }
}


impl LeanPath {

    pub fn new_with_args(args : &args::Args) -> io::Result<LeanPath> {
        let lib = args.library().unwrap_or_else(||
            panic!("can't find lean; use the -L switch to say where the lean root is"));
        LeanPath::new_with_lib(&lib) }

    pub fn new() -> io::Result<LeanPath> {
        let path = args::Args::lean_path().unwrap_or_else(||
            panic!("can't find lean; use the -L switch to say where the lean root is"));
        LeanPath::new_with_lib(&path)
    }

    pub fn new_with_lib(lib: &PathBuf) -> io::Result<LeanPath> {
        let path = get_leanpkg_path_file().unwrap_or_else(||
            panic!("can't find leanpkg.path; make sure you are in a lean project"));
        let mut res = Vec::new();
        let parent = path.parent().unwrap();
        res.push((parent.join("test"),DirScope::Project));
        for l in BufReader::new(File::open(&path)?).lines() {
            let l = l?;
            if l.starts_with("path ") {
                let path = String::from( &l[5..] );
                if path.starts_with("_target") {
                    res.push((parent.join(&path),DirScope::Library));
                } else  {
                    res.push((parent.join(&path),DirScope::Project));
                }
            } else if l == "builtin_path" {
                let mut lib1 = lib.clone(); lib1.push("library"); res.push((lib1,DirScope::Library));
                let mut lib2 = lib.clone(); lib2.push("lib"); lib2.push("lean"); lib2.push("library"); res.push((lib2,DirScope::Library));
            }
        }
        Ok(LeanPath(res))
    }

    pub fn make_relative(&self, p: &Path) -> Option<PathBuf> {
        for (ref dir,_) in &self.0 {
            if let Some(fp) = make_relative(dir,p) {
                return Some(fp) } }
        None
    }

    pub fn make_local(&self, p: &Path) -> Option<PathBuf> {
        for (ref dir,scope) in &self.0 {
            if let DirScope::Project = scope {
                if let Some(fp) = make_relative(dir,p) {
                    return Some(fp) } } }
        None
    }

    pub fn find_path(&self, p: &Path) -> Option<PathBuf> {
        for (ref dir,_) in &self.0 {
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
