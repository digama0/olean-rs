use super::traversal::DescendantResult::*;
use super::trie_node::TrieNode;
use super::{NibbleVec, SubTrie, SubTrieMut, Trie, TrieCommon, TrieKey, LastAncestorIter};

impl<V> Trie<V> {
    /// Create an empty Trie.
    pub fn new() -> Trie<V> {
        Trie {
            length: 0,
            node: TrieNode::new(),
        }
    }

    /// View the root of this trie as a SubTrie.
    pub fn root(&self) -> SubTrie<V> {
        SubTrie {
            prefix: NibbleVec::new(),
            node: &self.node,
        }
    }

    /// View the root of this trie as a SubTrieMut.
    pub fn root_mut(&mut self) -> SubTrieMut<V> {
        SubTrieMut {
            prefix: NibbleVec::new(),
            length: &mut self.length,
            node: &mut self.node,
        }
    }

    /// Fetch a reference to the given key's corresponding value, if any.
    pub fn get<K: TrieKey + ?Sized>(&self, key: &K) -> Option<&V> {
        self.get_nv(&key.encode())
    }

    /// Fetch a reference to the given key's corresponding value, if any.
    pub fn get_nv(&self, key: &NibbleVec) -> Option<&V> {
        self.node
            .get(&key)
            .and_then(|t| t.value())
    }

    /// Fetch a mutable reference to the given key's corresponding value, if any.
    pub fn get_mut<K: TrieKey + ?Sized>(&mut self, key: &K) -> Option<&mut V> {
        self.get_mut_nv(&key.encode())
    }

    /// Fetch a mutable reference to the given key's corresponding value, if any.
    pub fn get_mut_nv(&mut self, key: &NibbleVec) -> Option<&mut V> {
        self.node
            .get_mut(&key)
            .and_then(|t| t.value_mut())
    }

    /// Insert the given key-value pair, returning any previous value associated with the key.
    pub fn insert<K: TrieKey + ?Sized>(&mut self, key: &K, value: V) -> Option<V> {
        self.insert_nv(key.encode(), value)
    }

    /// Insert the given key-value pair, returning any previous value associated with the key.
    pub fn insert_nv(&mut self, key: NibbleVec, value: V) -> Option<V> {
        let result = self.node.insert(key, value);
        if result.is_none() {
            self.length += 1;
        }
        result
    }

    /// Remove the value associated with the given key.
    pub fn remove<K: TrieKey + ?Sized>(&mut self, key: &K) -> Option<V> {
        self.remove_nv(&key.encode())
    }

    /// Remove the value associated with the given key.
    pub fn remove_nv(&mut self, key: &NibbleVec) -> Option<V> {
        let removed = self.node.remove(key);
        if removed.is_some() {
            self.length -= 1;
        }
        removed
    }

    /// Get a mutable reference to the value stored at this node, if any.
    pub fn value_mut(&mut self) -> Option<&mut V> {
        self.node.value_mut()
    }

    /// Fetch a reference to the subtrie for a given key.
    pub fn subtrie<'a, K: TrieKey + ?Sized>(&'a self, key: &K) -> Option<SubTrie<'a, V>> {
        let key_fragments = key.encode();
        self.node
            .get(&key_fragments)
            .map(|node| node.as_subtrie(key_fragments))
    }

    /// Fetch a mutable reference to the subtrie for a given key.
    pub fn subtrie_mut<'a, K: TrieKey + ?Sized>(&'a mut self, key: &K) -> Option<SubTrieMut<'a, V>> {
        let key_fragments = key.encode();
        let length_ref = &mut self.length;
        self.node
            .get_mut(&key_fragments)
            .map(move |node| node.as_subtrie_mut(key_fragments, length_ref))
    }

    /// Fetch a reference to the closest ancestor node of the given key.
    ///
    /// If `key` is encoded as byte-vector `b`, return the node `n` in the tree
    /// such that `n`'s key's byte-vector is the longest possible prefix of `b`, and `n`
    /// has a value.
    ///
    /// Invariant: `result.is_some() => result.key_value.is_some()`.
    ///
    /// The key may be any borrowed form of the trie's key type, but TrieKey on the borrowed
    /// form *must* match those for the key type
    pub fn get_ancestor<'a, K: TrieKey + ?Sized>(&'a self, key: &K) -> Option<SubTrie<'a, V>> {
        let mut key_fragments = key.encode();
        self.node
            .get_ancestor(&key_fragments)
            .map(|(node, node_key_len)| {
                key_fragments.split(node_key_len);
                node.as_subtrie(key_fragments)
            })
    }

    /// Fetch the closest ancestor *value* for a given key.
    ///
    /// See `get_ancestor` for precise semantics, this is just a shortcut.
    ///
    /// The key may be any borrowed form of the trie's key type, but TrieKey on the borrowed
    /// form *must* match those for the key type
    pub fn get_ancestor_value<K: TrieKey + ?Sized>(&self, key: &K) -> Option<&V> {
        self.get_ancestor(key).and_then(|t| t.node.value())
    }

    /// The key may be any borrowed form of the trie's key type, but TrieKey on the borrowed
    /// form *must* match those for the key type
    pub fn get_raw_ancestor<'a, K: TrieKey + ?Sized>(&'a self, key: &K) -> SubTrie<'a, V> {
        let mut nv = key.encode();
        let (ancestor_node, depth) = self.node.get_raw_ancestor(&nv);
        nv.split(depth);
        ancestor_node.as_subtrie(nv)
    }

    /// Fetch the closest descendant for a given key.
    ///
    /// If the key is in the trie, this is the same as `subtrie`.
    ///
    /// The key may be any borrowed form of the trie's key type, but TrieKey on the borrowed
    /// form *must* match those for the key type
    pub fn get_raw_descendant<'a, K: TrieKey + ?Sized>(&'a self, key: &K) -> Option<SubTrie<'a, V>> {
        let mut nv = key.encode();
        self.node.get_raw_descendant(&nv).map(|desc| {
            let (node, prefix) = match desc {
                NoModification(node) => (node, nv),
                ExtendKey(node, depth, extension) => {
                    nv.split(depth);
                    (node, nv.join(extension))
                }
            };
            node.as_subtrie(prefix)
        })
    }

    /// Return a stream consumer that searches for the longest key in the trie that
    /// is an initial sequence of the stream, and has a value.
    ///
    /// Use `LastAncestorIter::next` and `LastAncestorIter::finish` to input key data
    /// to the iterator.
    pub fn last_ancestor_iter(&self) -> LastAncestorIter<V> {
        LastAncestorIter::new(&self.node)
    }

    /// Take a function `f` and apply it to the value stored at `key`.
    ///
    /// If no value is stored at `key`, store `default`.
    pub fn map_with_default<K: TrieKey + ?Sized, F: Fn(&mut V)>(&mut self, key: &K, f: F, default: V) {
        if let Some(v) = self.get_mut(key) {
            f(v);
            return;
        }
        self.insert(key, default);
    }

    /// Check that the Trie invariants are satisfied - you shouldn't ever have to call this!
    /// Quite slow!
    #[doc(hidden)]
    pub fn check_integrity(&self) -> bool {
        let (ok, length) = self.node.check_integrity_recursive(0);
        ok && length == self.length
    }
}

impl<V: PartialEq> PartialEq for Trie<V> {
    fn eq(&self, other: &Trie<V>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get_nv(&key).map_or(false, |v| *value == *v))
    }
}

impl<V> Default for Trie<V> {
    fn default() -> Self {
        Self::new()
    }
}
