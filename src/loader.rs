use std::collections::hash_map::HashMap;
use std::collections::BTreeSet;
use std::io;
use std::fs::File;
use crate::types::*;
use crate::deserialize;
use crate::leanpath::*;

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
            if map.contains_key(&n) { map.get_mut(&n)? }
            else { map.get_mut(&n.clone().str("default".to_string()))? };
        if let Some(mods) = o { return Some(mods) }
        let mods = deserialize::read_olean_modifications(&ol.code).unwrap_or_else(|err|
            panic!("error parsing {}: {}", n, err)
        );
        return Some(o.get_or_insert(mods)) }

    fn decls(m : &[Modification]) -> Vec<&Declaration> {
        let mut arr: Vec<&Declaration> = Vec::new();
        for x in m {
            if let Modification::Decl{ decl: d, trust_lvl: _ } = &x {
                arr.push(&d) } }
        arr }

    pub fn exported_syms(&mut self, n : &Name) -> Option<BTreeSet<Name>> {
        let b = Loader::decls(Loader::get_mods2(&mut self.map, n.clone()).expect("exported_syms"));
        let set: BTreeSet<Name> = b.iter().map(|d| d.name()).collect();
        Some(set) }

    pub fn used_syms(&mut self, n : &Name) -> Option<BTreeSet<Name>> {
        let b = Loader::decls(Loader::get_mods2(&mut self.map, n.clone()).expect("used_syms"));
        let mut set: BTreeSet<Name> = BTreeSet::new();
        for d in b {
            d.ref_symbols_acc(&mut set)
        }
        Some(set) }

    pub fn unused_imports(&mut self, n : &Name) -> Vec<Name> {
        let msg = format!("unknown module 1 {:?}", n);
        let s = self.used_syms(n).expect(msg.as_str());
        let msg = format!("unknown module 2 {:?}", n);
        let (ol,_) = self.map.get(&n).expect(msg.as_str());
        let n2 : Name = self.lean_path.find(n.clone(), "olean").expect(msg.as_str()).0;
        let imps : Vec<Name> = ol.imports.iter().map(|m| m.resolve(n2.clone())).collect();
        let mut r : Vec<Name> = Vec::new();
        for m in imps {
            if m != name![init] {
                let syms : BTreeSet<Name> = self.exported_syms(&m).expect(format!("unknown module {:?}", m).as_str());
                if syms.is_disjoint(&s) {
                    r.push(m.clone()) } }
        }
        r
    }
}
