use std::collections::HashMap;
use std::io;
use std::fs::File;
use super::types::*;
use super::deserialize;
use super::leanpath::*;

pub struct Loader {
    pub map: HashMap<Name, OLean>,
    pub order: Vec<Name>
}

fn load_olean(lp: &LeanPath, n: Name) -> io::Result<Option<OLean>> {
    Ok(if let Some(file) = lp.find(n.clone(), "olean") {
        Some(deserialize::read_olean(File::open(file)?)?)
    } else { None })
}

impl Loader {
    fn new() -> Loader { Loader { map: HashMap::new(), order: Vec::new() } }

    fn load_oleans_core(&mut self, lp: &LeanPath, start: Name) -> io::Result<()> {
        if let Some(ol) = load_olean(lp, start.clone())? {
            for mp in &ol.imports {
                let other = mp.resolve(start.clone());
                if !self.map.contains_key(&other) {
                    self.load_oleans_core(lp, other)?
                }
            }
            self.order.push(start.clone());
            self.map.insert(start, ol);
        } else { println!("can't find {}\npath = {:?}", start, lp.0) }
        Ok(())
    }

    pub fn load(lp: &LeanPath, start: Name) -> io::Result<Loader> {
        let mut l = Loader::new();
        l.load_oleans_core(lp, start)?;
        Ok(l)
    }
}
