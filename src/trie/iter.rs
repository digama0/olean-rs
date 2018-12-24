//! Iterators over key-value pairs, keys, values and child subtries.

use std::iter::{FilterMap, FromIterator, Map};
use std::slice;
use std::ops::Deref;

use super::trie_node::TrieNode;
use super::{NibbleVec, SubTrie, Trie, TrieKey};

// MY EYES.
type Child<V> = Box<TrieNode<V>>;
type RawChildIter<'a, V> = slice::Iter<'a, Option<Child<V>>>;
type ChildMapFn<'a, V> = fn(&'a Option<Child<V>>) -> Option<&'a Child<V>>;
type ChildIter<'a, V> = FilterMap<RawChildIter<'a, V>, ChildMapFn<'a, V>>;

/// Iterator over the keys and values of a Trie.
pub struct Iter<'a, V: 'a> {
    root: &'a TrieNode<V>,
    root_visited: bool,
    stack: Vec<ChildIter<'a, V>>,
}

impl<'a, V> Iter<'a, V> {
    // TODO: make this private somehow (and same for the other iterators).
    pub fn new(root: &'a TrieNode<V>) -> Iter<'a, V> {
        Iter {
            root: root,
            root_visited: false,
            stack: vec![],
        }
    }
}

/// Iterator over the keys of a Trie.
pub struct Keys<'a, V: 'a> {
    inner: Map<Iter<'a, V>, KeyMapFn<'a, V>>,
}

type KeyMapFn<'a, V> = fn((&'a NibbleVec, &'a V)) -> &'a NibbleVec;

impl<'a, V> Keys<'a, V> {
    pub fn new(iter: Iter<'a, V>) -> Keys<'a, V> {
        Keys {
            inner: iter.map(|kv| kv.0),
        }
    }
}

impl<'a, V> Iterator for Keys<'a, V> {
    type Item = &'a NibbleVec;

    fn next(&mut self) -> Option<&'a NibbleVec> {
        self.inner.next()
    }
}

/// Iterator over the values of a Trie.
pub struct Values<'a, V: 'a> {
    inner: Map<Iter<'a, V>, ValueMapFn<'a, V>>,
}

type ValueMapFn<'a, V> = fn((&'a NibbleVec, &'a V)) -> &'a V;

impl<'a, V> Values<'a, V> {
    pub fn new(iter: Iter<'a, V>) -> Values<'a, V> {
        Values {
            inner: iter.map(|kv| kv.1),
        }
    }
}

impl<'a, V> Iterator for Values<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        self.inner.next()
    }
}

/// Iterator over the child subtries of a trie.
pub struct Children<'a, V: 'a> {
    prefix: NibbleVec,
    inner: ChildIter<'a, V>,
}

impl<'a, V> Children<'a, V> {
    pub fn new(key: NibbleVec, node: &'a TrieNode<V>) -> Self {
        Children {
            prefix: key,
            inner: node.child_iter(),
        }
    }
}

impl<'a, V> Iterator for Children<'a, V> {
    type Item = SubTrie<'a, V>;

    fn next(&mut self) -> Option<SubTrie<'a, V>> {
        self.inner.next().map(|node| SubTrie {
            prefix: self.prefix.clone().join(&node.key),
            node: node,
        })
    }
}

impl<V> TrieNode<V> {
    /// Helper function to get all the non-empty children of a node.
    fn child_iter(&self) -> ChildIter<V> {
        fn id<V>(x: &Option<Child<V>>) -> Option<&Child<V>> {
            x.as_ref()
        }

        self.children.iter().filter_map(id)
    }

    /// Get the key and value of a node as a pair.
    fn kv_as_pair(&self) -> Option<(&NibbleVec, &V)> {
        self.value.as_ref().map(|v| (&self.key, v.deref()))
    }
}

enum IterAction<'a, V: 'a> {
    Push(&'a TrieNode<V>),
    Pop,
}

impl<'a, V> Iterator for Iter<'a, V> {
    type Item = (&'a NibbleVec, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        use self::IterAction::*;

        // Visit each node as it is reached from its parent (with special root handling).
        if !self.root_visited {
            self.root_visited = true;
            self.stack.push(self.root.child_iter());
            if let Some(kv) = self.root.kv_as_pair() {
                return Some(kv);
            }
        }

        loop {
            let action = match self.stack.last_mut() {
                Some(stack_top) => match stack_top.next() {
                    Some(child) => Push(child),
                    None => Pop,
                },
                None => return None,
            };

            match action {
                Push(trie) => {
                    self.stack.push(trie.child_iter());
                    if let Some(kv) = trie.kv_as_pair() {
                        return Some(kv);
                    }
                }
                Pop => {
                    self.stack.pop();
                }
            }
        }
    }
}

impl<K: TrieKey, V> FromIterator<(K, V)> for Trie<V> {
    fn from_iter<T>(iter: T) -> Trie<V>
    where
        T: IntoIterator<Item = (K, V)>,
    {
        let mut trie: Trie<V> = Trie::new();
        for (k, v) in iter {
            trie.insert(&k, v);
        }
        trie
    }
}
