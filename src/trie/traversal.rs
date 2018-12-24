//! This module contains the core algorithms.

use super::keys::{match_keys, KeyMatch};
use super::trie_node::TrieNode;
use super::NibbleVec;

use self::DescendantResult::*;

impl<V> TrieNode<V> {
    pub fn get(&self, key: &NibbleVec) -> Option<&TrieNode<V>> {
        iterative_get(self, key)
    }

    pub fn get_mut(&mut self, key: &NibbleVec) -> Option<&mut TrieNode<V>> {
        iterative_get_mut(self, key)
    }

    pub fn insert(&mut self, key: NibbleVec, value: V) -> Option<V> {
        iterative_insert(self, key, value)
    }

    pub fn remove(&mut self, key: &NibbleVec) -> Option<V> {
        recursive_remove(self, key)
    }

    pub fn get_ancestor(&self, key: &NibbleVec) -> Option<(&TrieNode<V>, usize)> {
        get_ancestor(self, key)
    }

    pub fn get_raw_ancestor(&self, key: &NibbleVec) -> (&TrieNode<V>, usize) {
        get_raw_ancestor(self, key)
    }

    pub fn get_raw_descendant<'a>(&'a self, key: &NibbleVec) -> Option<DescendantResult<'a, V>> {
        get_raw_descendant(self, key)
    }
}

macro_rules! id {
    ($e:item) => {
        $e
    };
}

macro_rules! get_func {
    (
        name: $name:ident,
        trie_type: $trie_type:ty,
        mutability: $($mut_:tt)*
    ) => {id!{
        fn $name<'a, V>(trie: $trie_type, key: &NibbleVec) -> Option<$trie_type> {
            if key.len() == 0 {
                return Some(trie);
            }

            let mut prev = trie;
            let mut depth = 0;

            loop {
                let bucket = key.get(depth) as usize;
                let current = prev;
                if let Some(ref $($mut_)* child) = current.children[bucket] {
                    match match_keys(depth, key, &child.key) {
                        KeyMatch::Full => {
                            return Some(child);
                        }
                        KeyMatch::SecondPrefix => {
                            depth += child.key.len();
                            prev = child;
                        }
                        _ => {
                            return None;
                        }
                    }
                } else {
                    return None;
                }
            }
        }
    }}
}

get_func!(name: iterative_get, trie_type: &'a TrieNode<V>, mutability: );
get_func!(name: iterative_get_mut, trie_type: &'a mut TrieNode<V>, mutability: mut);

fn iterative_insert<V>(
    trie: &mut TrieNode<V>,
    mut key: NibbleVec,
    value: V,
) -> Option<V> {
    if key.len() == 0 {
        return trie.replace_value(value);
    }

    let mut prev = trie;
    let mut depth = 0;

    loop {
        let bucket = key.get(depth) as usize;
        let current = prev;
        if let Some(ref mut child) = current.children[bucket] {
            match match_keys(depth, &key, &child.key) {
                KeyMatch::Full => {
                    return child.replace_value(value);
                }
                KeyMatch::Partial(idx) => {
                    // Split the existing child.
                    child.split(idx);

                    // Insert the new key below the prefix node.
                    let new_key = key.split(depth + idx);
                    let new_key_bucket = new_key.get(0) as usize;

                    child.add_child(
                        new_key_bucket,
                        Box::new(TrieNode::with_key_value(new_key, value)),
                    );

                    return None;
                }
                KeyMatch::FirstPrefix => {
                    child.split(key.len() - depth);
                    child.add_value(value);
                    return None;
                }
                KeyMatch::SecondPrefix => {
                    depth += child.key.len();
                    prev = child;
                }
            }
        } else {
            let node_key = key.split(depth);
            current.add_child(
                bucket,
                Box::new(TrieNode::with_key_value(node_key, value)),
            );
            return None;
        }
    }
}

// TODO: clean this up and make it iterative.
fn recursive_remove<V>(trie: &mut TrieNode<V>, key: &NibbleVec) -> Option<V> {
    if key.len() == 0 {
        return trie.take_value();
    }

    let bucket = key.get(0) as usize;

    let child = trie.take_child(bucket);

    match child {
        Some(mut child) => {
            match match_keys(0, &key, &child.key) {
                KeyMatch::Full => {
                    let result = child.take_value();
                    if child.child_count != 0 {
                        // If removing this node's value has made it a value-less node with a
                        // single child, then merge its child.
                        let repl = if child.child_count == 1 {
                            get_merge_child(&mut child)
                        } else {
                            child
                        };
                        trie.add_child(bucket, repl);
                    }
                    result
                }
                KeyMatch::SecondPrefix => {
                    let depth = child.key.len();
                    rec_remove(trie, child, bucket, key, depth)
                }
                _ => None,
            }
        }
        None => None,
    }
}

fn get_merge_child<V>(trie: &mut TrieNode<V>) -> Box<TrieNode<V>> {
    let mut child = trie.take_only_child();

    // Join the child's key onto the existing one.
    child.key = trie.key.clone().join(&child.key);

    child
}

// Tail-recursive remove function used by `recursive_remove`.
fn rec_remove<V>(
    parent: &mut TrieNode<V>,
    mut middle: Box<TrieNode<V>>,
    prev_bucket: usize,
    key: &NibbleVec,
    depth: usize,
) -> Option<V> {
    let bucket = key.get(depth) as usize;

    let child = middle.take_child(bucket);
    parent.add_child(prev_bucket, middle);

    match child {
        Some(mut child) => {
            let middle = parent.children[prev_bucket].as_mut().unwrap();
            match match_keys(depth, key, &child.key) {
                KeyMatch::Full => {
                    let result = child.take_value();

                    // If this node has children, keep it.
                    if child.child_count != 0 {
                        // If removing this node's value has made it a value-less node with a
                        // single child, then merge its child.
                        let repl = if child.child_count == 1 {
                            get_merge_child(&mut *child)
                        } else {
                            child
                        };
                        middle.add_child(bucket, repl);
                    }
                    // Otherwise, if the parent node now only has a single child, merge it.
                    else if middle.child_count == 1 && middle.value.is_none() {
                        let repl = get_merge_child(middle);
                        *middle = repl;
                    }

                    result
                }
                KeyMatch::SecondPrefix => {
                    let new_depth = depth + child.key.len();
                    rec_remove(middle, child, bucket, key, new_depth)
                }
                _ => None,
            }
        }
        None => None,
    }
}

fn get_ancestor<'a, V>(
    trie: &'a TrieNode<V>,
    key: &NibbleVec,
) -> Option<(&'a TrieNode<V>, usize)> {
    if key.len() == 0 {
        return trie.as_value_node().map(|node| (node, 0));
    }

    let mut prev = trie;
    // The ancestor is such that all nodes upto and including `prev` have
    // already been considered.
    let mut ancestor = prev.as_value_node();
    let mut depth = 0;

    loop {
        let bucket = key.get(depth) as usize;
        let current = prev;
        if let Some(ref child) = current.children[bucket] {
            match match_keys(depth, key, &child.key) {
                KeyMatch::Full => {
                    return child
                        .as_value_node()
                        .map(|node| (node, depth + node.key.len()))
                        .or_else(|| ancestor.map(|anc| (anc, depth)));
                }
                KeyMatch::FirstPrefix | KeyMatch::Partial(_) => {
                    return ancestor.map(|anc| (anc, depth));
                }
                KeyMatch::SecondPrefix => {
                    depth += child.key.len();
                    ancestor = child.as_value_node().or(ancestor);
                    prev = child;
                }
            }
        } else {
            return ancestor.map(|anc| (anc, depth));
        }
    }
}

fn get_raw_ancestor<'a, V>(
    trie: &'a TrieNode<V>,
    key: &NibbleVec,
) -> (&'a TrieNode<V>, usize) {
    if key.len() == 0 {
        return (trie, 0);
    }

    let mut prev = trie;
    // The ancestor is such that all nodes upto and including `prev` have
    // already been considered.
    let mut ancestor = prev;
    let mut depth = 0;

    loop {
        let bucket = key.get(depth) as usize;
        let current = prev;
        if let Some(ref child) = current.children[bucket] {
            match match_keys(depth, key, &child.key) {
                KeyMatch::Full => {
                    return (child, depth + child.key.len());
                }
                KeyMatch::FirstPrefix | KeyMatch::Partial(_) => {
                    return (ancestor, depth);
                }
                KeyMatch::SecondPrefix => {
                    depth += child.key.len();
                    ancestor = child;
                    prev = child;
                }
            }
        } else {
            return (ancestor, depth);
        }
    }
}

// Type used to propogate subtrie construction instructions to the top-level `get_raw_descendant`
// method.
pub enum DescendantResult<'a, V: 'a> {
    NoModification(&'a TrieNode<V>),
    ExtendKey(&'a TrieNode<V>, usize, &'a NibbleVec),
}

fn get_raw_descendant<'a, V>(
    trie: &'a TrieNode<V>,
    key: &NibbleVec,
) -> Option<DescendantResult<'a, V>> {
    if key.len() == 0 {
        return Some(NoModification(trie));
    }

    let mut prev = trie;
    let mut depth = 0;

    loop {
        let bucket = key.get(depth) as usize;
        let current = prev;
        if let Some(ref child) = current.children[bucket] {
            match match_keys(depth, key, &child.key) {
                KeyMatch::Full => {
                    return Some(NoModification(child));
                }
                KeyMatch::FirstPrefix => {
                    return Some(ExtendKey(child, depth, &child.key));
                }
                KeyMatch::SecondPrefix => {
                    depth += child.key.len();
                    prev = child;
                }
                _ => {
                    return None;
                }
            }
        } else {
            return None;
        }
    }
}
