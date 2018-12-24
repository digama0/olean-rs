//! This module contains an iterator-like interface to a longest-key search.
//!
//! Given a fixed Trie representing a set of keys, we want to find the longest
//! key in the Trie that matches an initial sequence of the input key stream.
//! The input key is fed piecemeal, though; we keep track of the search in progress
//! and report whether we have seen enough of the stream to determine the answer,
//! or if we need more data.

use super::{NibbleVec, TrieNode, TrieKey};
use super::keys::{match_keys, KeyMatch};

#[derive(Debug)]
pub struct LastAncestorIter<'a, V> {
    trie: &'a TrieNode<V>,
    best: Option<(&'a V, usize)>,
    depth: usize,
    progress: usize
}

type SearchResult<'a, V> = Result<Option<(&'a V, usize)>, LastAncestorIter<'a, V>>;

impl<'a, V> LastAncestorIter<'a, V> {
    /// Create a new iterator.
    pub fn new(trie: &TrieNode<V>) -> LastAncestorIter<V> {
        LastAncestorIter { trie, best: None, depth: trie.key.len(), progress: 0 }
    }

    /// Input some key data into the iterator. Returns either `Done(res)`
    /// if the search is finished, and `res` is the value and length of the
    /// longest initial sequence of the key stream with a value, or `Next(iter)`
    /// to request more data from the stream with `iter` as the continuation.
    pub fn next<K: TrieKey + ?Sized>(self, key: &K) -> SearchResult<'a, V> {
        self.next_nv(&key.encode())
    }

    /// Input some key data into the iterator. Returns either `Done(res)`
    /// if the search is finished, and `res` is the value and length of the
    /// longest initial sequence of the key stream with a value, or `Next(iter)`
    /// to request more data from the stream with `iter` as the continuation.
    pub fn next_nv(mut self, key: &NibbleVec) -> SearchResult<'a, V> {
        match match_keys(self.progress, &self.trie.key, key) {
            KeyMatch::Partial(_) => return Ok(self.best),
            KeyMatch::SecondPrefix | KeyMatch::Full => {
                self.progress += key.len();
                return Err(self)
            },
            KeyMatch::FirstPrefix => {
                let mut depth = self.trie.key.len() - self.progress;
                loop {
                    if let Some(v) = self.trie.value() {
                        self.best = Some((v, self.depth));
                    }
                    let bucket = key.get(depth) as usize;
                    if let Some(ref child) = self.trie.children[bucket] {
                        self.trie = child;
                        self.depth += child.key.len();
                        match match_keys(depth, key, &child.key) {
                            KeyMatch::SecondPrefix => {
                                depth += child.key.len();
                            }
                            KeyMatch::FirstPrefix | KeyMatch::Full => {
                                self.progress = key.len() - depth;
                                return Err(self)
                            }
                            KeyMatch::Partial(_) => return Ok(self.best),
                        }
                    } else {
                        return Ok(self.best)
                    }
                }
            }
        }
    }

    /// Input an EOF to the iterator, forcing it to give the best result it
    /// has found so far.
    pub fn finish(mut self) -> Option<(&'a V, usize)> {
        if self.trie.key.len() == self.progress {
            if let Some(v) = self.trie.value() {
                self.best = Some((v, self.depth))
            }
        }
        self.best
    }
}
