// use std::vec::Vec;
use std::collections::hash_map::HashMap;
use std::hash::Hash;
// use std::ops::Deref;
// use std::ops::Index;
// use core::iter::FromIterator;

pub struct DisjSets<T> {
    parent: Vec<usize>,
    size: Vec<i32>,
    idx: HashMap<T,usize> }

fn root_inner(parent : &mut Vec<usize>, x: usize) -> usize {
    let mut i = x;
    while i != parent[i] {
        let prev = i;
        i = parent[i];
        parent[prev] = parent[i] }
    i }

impl <T> DisjSets<T>
where T : Hash, T: Eq, T : Clone, T : core::fmt::Debug {
    pub fn new() -> DisjSets<T> {
        DisjSets { parent: Vec::new(),
                   size: Vec::new(),
                   // vals: Vec::new(),
                   idx: HashMap::new() } }
    fn get_index (&mut self, x: &T) -> usize {
        if let Some(i) = self.idx.get(x) {
            *i
        } else {
            let i = self.parent.len();
            self.parent.push(i);
            self.size.push(1);
            // self.vals.push((*x).clone());
            self.idx.insert((*x).clone(), i);
            i } }
    fn root(&mut self, x: &T) -> usize {
        let i = self.get_index(x);
        root_inner(&mut self.parent, i) }
    pub fn merge(&mut self, x: &T, y: &T) {
        let mut i = self.root(x);
        let mut j = self.root(y);
        if i == j { return }
        if self.size[i] < self.size[j] {
            std::mem::swap(&mut i, &mut j)
        }
        self.parent[j] = i;
        self.size[i] = self.size[i] + self.size[j];
        let i2 = self.get_index(x);
        let j2 = self.get_index(y);
        assert!(self.same_set(x,y), format!("{:?} ({}, {}), {:?} ({}, {}), - {:?}", x, i, i2, y, j, j2, self.parent)) }
    pub fn same_set(&mut self, x : &T, y : &T) -> bool {
        let i = self.root(x);
        let j = self.root(y);
        i == j }
    pub fn list_sets(&mut self) -> Vec<Vec<T>> {
        let mut h : HashMap<usize, Vec<T>> = HashMap::new();
        for (x,i) in &self.idx {
            let j = root_inner(&mut self.parent, *i);
            if let Some(v) = h.get_mut(&j) { v.push(x.clone()) }
            else {
                let mut v = Vec::new();
                v.push(x.clone());
                h.insert(j,v); } }
        h.drain().map(|x| x.1).collect() }

}
