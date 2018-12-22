use std::collections::hash_map::HashMap;
use std::io;
use std::fs::File;
use super::types::*;
use super::deserialize;
use super::leanpath::*;

pub struct Loader {
    pub map: HashMap<Name, (OLean, Option<Vec<Modification>>)>,
    pub order: Vec<Name>
}

fn load_olean(lp: &LeanPath, n: Name) -> io::Result<Option<(Name, OLean)>> {
    Ok(if let Some((n2, file)) = lp.find(n.clone(), "olean") {
        Some((n2, deserialize::read_olean(File::open(file)?)?))
    } else { None })
}

impl Loader {
    fn new() -> Loader { Loader { map: HashMap::new(), order: Vec::new() } }

    fn load_oleans_core(&mut self, lp: &LeanPath, start: Name) -> io::Result<()> {
        if let Some((n2, ol)) = load_olean(lp, start.clone())? {
            for mp in &ol.imports {
                let other = mp.resolve(n2.clone());
                if !self.map.contains_key(&other) {
                    self.load_oleans_core(lp, other)?
                }
            }
            self.order.push(n2.clone());
            self.map.insert(n2, (ol, None));
        } else { println!("can't find {}\npath = {:?}", start, lp.0) }
        Ok(())
    }

    pub fn load(lp: &LeanPath, start: Name) -> io::Result<Loader> {
        let mut l = Loader::new();
        l.load_oleans_core(lp, start)?;
        Ok(l)
    }

    pub fn get_mods(map: &mut HashMap<Name, (OLean, Option<Vec<Modification>>)>, n: Name) -> io::Result<&[Modification]> {
        let (ol, o) = map.get_mut(&n).expect("should already be loaded");
        if let Some(mods) = o { return Ok(mods) }
        let mods = deserialize::read_olean_modifications(&ol.code).map_err(|err| {
            io::Error::new(io::ErrorKind::InvalidData, format!("error parsing {}: {}", n, err))
        })?;
        Ok(o.get_or_insert(mods))
    }
}
