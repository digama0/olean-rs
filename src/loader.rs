use std::collections::hash_map::HashMap;
use std::collections::BTreeSet;
use std::collections::LinkedList;
use std::iter::*;
use std::io;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::fs::File;
use crate::types::*;
use crate::deserialize;
use crate::leanpath::*;
use crate::union_find::*;

pub struct Loader {
    pub map: HashMap<Name, (OLean, Option<Vec<Modification>>)>,
    pub order: Vec<Name>,
    pub lean_path: LeanPath
}

fn load_olean(lp: &LeanPath, n: Name) -> io::Result<Option<(Name, OLean)>> {
    Ok(if let Some((n2, file)) = lp.find(n.clone(), "olean") {
        Some((n2, deserialize::read_olean(File::open(file)?)?))
    } else { None })
}

fn decl_prism(d : &Modification) -> Option<&Declaration> {
    if let Modification::Decl{ decl: d, trust_lvl: _ } = &d {
        Some(&d)
    } else { None } }

#[derive(Debug)]
pub struct Advice {
    pub module : Vec<Name>,
    pub replacement : Vec<Name> }

impl Display for Advice {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let xs : Vec<String> = self.module.iter().map(|x| format!("{:?}", x)).collect();
        write!(f, "{}\n", xs.join (", imported by "))?;
        if self.replacement.is_empty() {
            write!(f, "  - delete import")
        } else {
            write!(f, "  - replace with\n")?;
            let xs : Vec<String> = self.replacement.iter().map(|x| format!("{:?}", x)).collect();
            write!(f, "       import {}", xs.join ("\n              ")) }
    }
}

impl Loader {
    pub fn new(lp: LeanPath) -> Loader { Loader { map: HashMap::new(), order: Vec::new(), lean_path: lp } }

    pub fn load(&mut self, start: Name) -> io::Result<()> {
        if let Some((n2, ol)) = load_olean(&self.lean_path, start.clone())? {
            for mp in &ol.imports {
                let other = mp.resolve(n2.clone());
                if !self.map.contains_key(&other) {
                    self.load(other)?
                }
            }
            self.order.push(n2.clone());
            self.map.insert(n2, (ol, None));
        } else { println!("can't find {}\npath = {:?}", start, self.lean_path.0) }
        Ok(())
    }

    pub fn get_mods(map: &mut HashMap<Name, (OLean, Option<Vec<Modification>>)>, n: Name) -> io::Result<&[Modification]> {
        let (ol, o) = map.get_mut(&n).expect("should already be loaded");
        if let Some(mods) = o { return Ok(mods) }
        let mods = deserialize::read_olean_modifications(&ol.code).map_err(|err| {
            io::Error::new(io::ErrorKind::InvalidData, format!("error parsing {}: {}", n, err))
        })?;
        Ok(o.get_or_insert(mods))
    }

    pub fn get_mods2(map: &mut HashMap<Name, (OLean, Option<Vec<Modification>>)>, n: Name) -> Option<&[Modification]> {
        let (ol, o) =
            if map.contains_key(&n) { map.get_mut(&n).expect("get_mods2: key not found") }
        else {
            println!("not found: {:?}", n);
            map.get_mut(&n.clone().str("default".to_string()))? };
        if let Some(mods) = o { return Some(mods) }
        let mods = deserialize::read_olean_modifications(&ol.code).unwrap_or_else(|err|
            panic!("error parsing {}: {}", n, err)
        );
        return Some(o.get_or_insert(mods)) }

    fn type_decls(m : &[Modification]) -> Vec<&InductiveDefn> {
        let mut arr: Vec<&InductiveDefn> = Vec::new();
        for x in m {
            if let Modification::Inductive{ defn: d, trust_lvl: _ } = &x {
                arr.push(&d) } }
        arr }

    fn class_entry(m : &[Modification]) -> Vec<&ClassEntry> {
        let mut arr: Vec<&ClassEntry> = Vec::new();
        for x in m {
            if let Modification::Class(entry) = &x {
                arr.push(&entry) } }
        arr }

    fn attributes(m : &[Modification]) -> Vec<&AttrEntry> {
        let mut arr: Vec<&AttrEntry> = Vec::new();
        for x in m {
            if let Modification::Attr(entry) = &x {
                arr.push(&entry) } }
        arr }

    fn user_attributes(m : &[Modification]) -> Vec<Name> {
        let mut arr: Vec<Name> = Vec::new();
        for x in m {
            if let Modification::UserAttribute(entry) = &x {
                arr.push(entry.clone()) } }
        arr }

    pub fn exported_syms(&mut self, n : &Name) -> BTreeSet<Name> {
        let mods = Loader::get_mods2(&mut self.map, n.clone()).expect("exported_syms");
        let decls = mods.iter().filter_map(decl_prism);
        let type_decl = Loader::type_decls(mods);
        let attributes = Loader::attributes(mods);
        let user_attributes = Loader::user_attributes(mods);
        let class_entry = Loader::class_entry(mods);
        let set: BTreeSet<Name> =
            decls.map(|d| d.name())
            .chain(type_decl.iter().map(|d| d.name()))
            .chain(user_attributes.iter().cloned())
            .chain(attributes.iter().flat_map(|d| d.names()))
            .chain(class_entry.iter().map(|d| d.name()))
            .collect();
        set }

    pub fn used_syms(&mut self, n : &Name) -> BTreeSet<Name> {
        let mods = Loader::get_mods2(&mut self.map, n.clone()).expect("used_syms");
        let decls = mods.iter().filter_map(decl_prism);
        let mut set: BTreeSet<Name> = BTreeSet::new();
        for d in decls {
            d.ref_symbols_acc(&mut set)
        }
        for attr in Loader::attributes(mods).iter().flat_map(|d| d.names()) {
            set.insert(attr); }
        set }

    pub fn iter_imports(&mut self, n : &Name) -> std::slice::Iter<ModuleName> {
        let msg = format!("unknown module 1 {:?}", n);
        let (ol,_) = self.map.get(&n).expect(msg.as_str());
        ol.imports.iter()
    }
    fn get_module(&self, n : &Name) -> &(OLean, Option<Vec<Modification>>) {
        self.map.get(&n).expect(format!("unknown module: {:?}", n).as_str()) }

    pub fn find_cliques(&mut self, n : &Name) -> Vec<(Vec<Name>,BTreeSet<Name>)> {
        let imports : Vec<Name> = self.get_module(n).0.imports.iter().map(|m| m.resolve(n.clone())).collect();
        let interfaces : HashMap<Name,BTreeSet<Name>> = imports.iter().map(
            |m| { let s = self.exported_syms(&m);
                  (m.clone(), s)}).collect();
        let mods = Loader::get_mods2(&mut self.map, n.clone()).expect("exported_syms");
        let decls : Vec<&Declaration> = mods.iter().filter_map(decl_prism).collect();
        let mut supp : HashMap<Name,(&Declaration,BTreeSet<Name>)> = HashMap::new();
        for d in decls {
            let mut imps : Vec<Name> = Vec::new();
            let refs = d.ref_symbols();
            for (m,syms) in &interfaces {
                if !refs.is_disjoint(&syms) { imps.push(m.clone()) } }
            supp.insert(d.name(), (d, imps.iter().cloned().collect()));  }
        let mut cl : DisjSets<Name> = DisjSets::new();
        for (d0,m0) in &supp {
            let refs = m0.0.ref_symbols();
            for (d1,m1) in &supp {
                if (m0.1.is_empty() && m1.1.is_empty()) || !m0.1.is_disjoint(&m1.1) || refs.contains(d1) {
                    cl.merge(d0, d1);
                    // assert!(cl.same_set(d0,d1), format!("{} - {}", d0, d1))
                } } }
        cl.list_sets().drain(0..).map(
            |set| { let imps : BTreeSet<Name> =
                    set.iter().fold(BTreeSet::new(),
                                    |mut x, y| {
                                        let r = supp.get_mut(&y).expect("wrong");
                                        x.append(&mut r.1); x });
                    (set,imps) } ).collect()
    }

    pub fn unused_imports(&mut self, n : &Name) -> Vec<Advice> {
        let s = self.used_syms(n);
        let tactic : Name = name![tactic];
        if s.iter().any(|n| tactic.is_prefix_of(&n)) ||
            n.drop_prefix() == name![default]
        { return Vec::new() }
        let mut path = LinkedList::new();
        let mut result = Vec::new();
        self.unused_imports_acc(n,&s,&mut path,&mut result);
        result }

    fn find_replacement(&mut self, n : &Name, s : &BTreeSet<Name>, rep : &mut BTreeSet<Name>) -> BTreeSet<Name> {
        let tactic : Name = name![tactic];
        let msg = format!("unknown module 3 {:?}", n);
        let (ol,_) = self.map.get(&n).expect(msg.as_str());
        let n2 : Name = self.lean_path.find(n.clone(), "olean").expect(msg.as_str()).0;
        let imps : Vec<Name> = ol.imports.iter().map(|m| m.resolve(n2.clone())).collect();
        for m in &imps {
            if *m != name![init] {
                let def_name = m.clone().str("default".to_string());
                if m.drop_prefix() == name![default] {
                    let mut rep2 = BTreeSet::new();
                    let mut ms = self.find_replacement(&m, s, &mut rep2);
                    if ms == rep2 {
                        rep.insert(m.clone());
                    } else { rep.append(&mut ms) }
                } else if self.map.contains_key(&def_name) {
                    let mut rep2 = BTreeSet::new();
                    let mut ms = self.find_replacement(&def_name, s, &mut rep2);
                    if ms == rep2 {
                        rep.insert(m.clone());
                    } else { rep.append(&mut ms) }
                } else {
                    let syms : BTreeSet<Name> = self.exported_syms(&m);
                    if syms.is_disjoint(&s) && !syms.iter().any(|n| tactic.is_prefix_of(&n)) {
                        // let mut rep: Vec<Name> = Vec::new();
                        self.find_replacement(&m,s,rep);
                        // rep.sort(); rep.dedup();
                        // result.push(Advice { module : path.iter().cloned().collect(),
                        //                      replacement : rep });
                    } else {
                        rep.insert(m.clone());
                    } } } }
        imps.iter().cloned().collect()
    }

    fn unused_imports_acc(&mut self, n : &Name, s : &BTreeSet<Name>, path : &mut LinkedList<Name>, result : &mut Vec<Advice>) {
        let tactic : Name = name![tactic];
        let msg = format!("unknown module 2 {:?}", n);
        let (ol,_) = self.map.get(&n).expect(msg.as_str());
        let n2 : Name = self.lean_path.find(n.clone(), "olean").expect(msg.as_str()).0;
        let imps : Vec<Name> = ol.imports.iter().map(|m| m.resolve(n2.clone())).collect();
        for m in imps {
            if m != name![init] {
                let syms : BTreeSet<Name> = self.exported_syms(&m);
                path.push_front(m.clone());
                let def_name = m.clone().str("default".to_string());
                if m.drop_prefix() == name![default] {
                    self.unused_imports_acc(&m, s, path, result)
                } else if self.map.contains_key(&def_name) {
                    self.unused_imports_acc(&def_name, s, path, result)
                } else {
                    if syms.is_disjoint(&s) && !syms.iter().any(|n| tactic.is_prefix_of(&n)) {
                        let mut rep: BTreeSet<Name> = BTreeSet::new();
                        self.find_replacement(&m,s,&mut rep);
                        // rep.sort(); rep.dedup();
                        result.push(Advice { module : path.iter().cloned().collect(),
                                             replacement : rep.iter().cloned().collect() });
                    }
                    // else { println!("- <skip>") }
                }
                path.pop_front(); } } }

    pub fn get_interface(&mut self, n : &Name) -> HashMap<Name,(Symbol,Visibility,bool)> {
        use Visibility::*;
        use Symbol::*;
        let mut res = HashMap::new();
        let mods = Loader::get_mods2(&mut self.map, n.clone()).unwrap();
        for x in mods {
            match x {
                Modification::Inductive{ defn: d, .. } => { res.insert(d.name(),(Type,Public,false)); },
                Modification::Decl{ decl: d, .. } => {
                    match d {
                        Declaration::Ax  { name: n, .. } => { res.insert(n.clone(),(Theorem,Public,false)); },
                        Declaration::Cnst{ name: n, .. } => { res.insert(n.clone(),(Def,Public,false)); },
                        Declaration::Defn{ name: n, ty: t, .. } => {
                            if is_tactic_type(t) && name![tactic.interactive].is_prefix_of(n) {
                                res.insert(n.clone(),(UserTactic,Public,false));
                            } else {
                                res.insert(n.clone(),(Def,Public,false)); } },
                        Declaration::Thm { name: n, .. } => { res.insert(n.clone(),(Theorem,Public,false)); }
                    }
                },
                Modification::Private{ name: _n, real: rn } => { if let Some(x) = res.get_mut(rn) { x.1 = Private; } },
                Modification::Protected(n) => { if let Some(x) = res.get_mut(n) { x.1 = Protected; } },
                Modification::Class(ClassEntry::Class(c)) => { res.insert(c.clone(),(Class,Public,false)); },
                // Modification::UserCommand(n) => { },
                Modification::Doc(n,_) => { res.get_mut(n).expect(format!("{:?} not found", n).as_str()).2 = true; },
                _ => { }
            }
        }
        res
    }
}

#[derive(PartialEq, Debug)]
pub enum Visibility {
    Public, Protected, Private }

#[derive(Debug)]
pub enum Symbol {
    Def, Theorem,
    UserTactic, Type,
    Class
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Symbol::*;
        match self {
            Def => write!(f, "Definition"),
            Theorem => write!(f, "Theorem"),
            UserTactic => write!(f, "User tactic"),
            Type => write!(f, "Type"),
            Class => write!(f, "Class") } } }

// #[test]
// #[nowarn(unused_imports)]
#[cfg(test)]
mod test {
    // use crate::leanpath::*;
    use crate::loader::*;
    use crate::lint::*;
    // use crate::args::*;
    use std::path::*;
    use std::env;

    #[test]
    pub fn test_get_interface () {
        env::set_current_dir("test").unwrap();
        let file : PathBuf = PathBuf::from( "simple4.olean" );
        let lp = LeanPath::new().unwrap_or_else(|e| panic!("problem: {}", e));
        let name = path_to_name(&lp, file.as_path())
            .expect(format!("cannot resolve path: {:?}", file).as_str());
        let mut load = Loader::new(lp);
        load.load(name.clone()).expect("load");
        let _r = load.get_interface(&name);
    }
    #[test]
    pub fn test_check_doc_string () {
        env::set_current_dir("test").unwrap();
        let file : PathBuf = PathBuf::from( "simple4.olean" );
        let lp = LeanPath::new().unwrap_or_else(|e| panic!("problem: {}", e));
        LeantConfig::write_config(&LeantConfig {
            unused_imports : false,
            doc_string_for_classes : true,
            .. LeantConfig::DEFAULT }).unwrap_or_else(|e| panic!("problem: {}", e));
        // let name = path_to_name(&lp, file.as_path())
        //     .expect(format!("cannot resolve path: {:?}", file).as_str());
        // let mut load = Loader::new(lp);
        // load.load(name.clone()).expect("load");
        println!("{:?}", run_checkers(&file, lp));
        panic!("foo");
    }
}
