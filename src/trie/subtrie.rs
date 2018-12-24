use super::keys::*;
use super::trie_node::TrieNode;
use super::{NibbleVec, SubTrie, SubTrieMut, SubTrieResult};

impl<'a, V> SubTrie<'a, V> {
    /// Look up the value for the given key, which should be an extension of this subtrie's key.
    ///
    /// The key may be any borrowed form of the trie's key type, but TrieKey on the borrowed
    /// form *must* match those for the key type
    pub fn get<K: TrieKey>(&self, key: &K) -> SubTrieResult<&V> {
        subtrie_get(&self.prefix, self.node, key)
    }

    /// Move the view to a subkey. The new view will be looking at the original key with
    /// the encoding of this subkey appended.
    pub fn to_subkey<K: TrieKey>(self, subkey: &K) -> Option<SubTrie<'a, V>> {
        self.to_subkey_nv(&subkey.encode())
    }

    /// Move the view to a subkey, specified directly by its `NibbleVec` encoding.
    /// The input view is consumed.
    pub fn to_subkey_nv(self, subkey: &NibbleVec) -> Option<SubTrie<'a, V>> {
        match self {
            SubTrie {prefix, node} =>
                node.get(subkey).map(|node|
                    SubTrie {
                        prefix: prefix.join(subkey),
                        node
                    })
        }
    }
}

fn subtrie_get<'a, K: TrieKey, V>(
    prefix: &NibbleVec,
    node: &'a TrieNode<V>,
    key: &K,
) -> SubTrieResult<&'a V> {
    let key_enc = key.encode();
    match match_keys(0, prefix, &key_enc) {
        KeyMatch::Full => Ok(node.value()),
        KeyMatch::FirstPrefix => Ok(node
            .get(&stripped(key_enc, prefix))
            .and_then(TrieNode::value)),
        _ => Err(()),
    }
}

impl<'a, V> SubTrieMut<'a, V> {
    /// Mutable reference to the node's value.
    pub fn value_mut(&mut self) -> Option<&mut V> {
        self.node.value_mut()
    }

    /// Look up the value for the given key, which should be an extension of this subtrie's key.
    ///
    /// The key may be any borrowed form of the trie's key type, but TrieKey on the borrowed
    /// form *must* match those for the key type
    pub fn get<K: TrieKey>(&self, key: &K) -> SubTrieResult<&V> {
        subtrie_get(&self.prefix, &*self.node, key)
    }

    /// Move the view to a subkey. The new view will be looking at the original key with
    /// the encoding of this subkey appended.
    pub fn to_subkey<K: TrieKey>(self, subkey: &K) -> Option<SubTrieMut<'a, V>> {
        self.to_subkey_nv(&subkey.encode())
    }

    /// Move the view to a subkey, specified directly by its `NibbleVec` encoding.
    /// The input view is consumed.
    pub fn to_subkey_nv(self, subkey: &NibbleVec) -> Option<SubTrieMut<'a, V>> {
        match self {
            SubTrieMut {length, prefix, node} =>
                node.get_mut(subkey).map(move |node|
                    SubTrieMut {
                        length,
                        prefix: prefix.join(subkey),
                        node
                    })
        }
    }

    /// Insert a value in this subtrie. The key should be an extension of this subtrie's key.
    pub fn insert<K: TrieKey>(&mut self, key: &K, value: V) -> SubTrieResult<V> {
        let key_enc = key.encode();
        let previous = match match_keys(0, &self.prefix, &key_enc) {
            KeyMatch::Full => self.node.replace_value(value),
            KeyMatch::FirstPrefix => self
                .node
                .insert(stripped(key_enc, &self.prefix), value),
            _ => {
                return Err(());
            }
        };

        if previous.is_none() {
            *self.length += 1;
        }

        Ok(previous)
    }

    /// Remove a value from this subtrie. The key should be an extension of this subtrie's key.
    pub fn remove<K: TrieKey>(&mut self, key: &K) -> SubTrieResult<V> {
        self.remove_nv(&key.encode())
    }

    /// Remove a value from this subtrie. The key should be an extension of this subtrie's key.
    pub fn remove_nv(&mut self, key: &NibbleVec) -> SubTrieResult<V> {
        let removed = match match_keys(0, &self.prefix, key) {
            KeyMatch::Full => self.node.take_value(),
            KeyMatch::FirstPrefix => self.node.remove(key),
            _ => {
                return Err(());
            }
        };

        if removed.is_some() {
            *self.length -= 1;
        }

        Ok(removed)
    }
}

fn stripped(mut key: NibbleVec, prefix: &NibbleVec) -> NibbleVec {
    key.split(prefix.len())
}
