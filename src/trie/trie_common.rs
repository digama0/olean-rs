use super::iter::*;
use super::trie_node::TrieNode;
use super::{NibbleVec, SubTrie, SubTrieMut, Trie};

/// Common functionality available for tries and subtries.
pub trait TrieCommon<'a, V: 'a>: ContainsTrieNode<'a, V>
where
    Self: Sized,
{
    /// Get the key stored at this node, if any.
    fn key(self) -> &'a NibbleVec {
        &self.trie_node().key
    }

    /// Get the value stored at this node, if any.
    fn value(self) -> Option<&'a V> {
        self.trie_node().value()
    }

    /// Number of key/value pairs stored in this trie.
    fn len(self) -> usize;

    /// Determine if the Trie contains 0 key-value pairs.
    fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Determine if the trie is a leaf node (has no children).
    fn is_leaf(self) -> bool {
        self.trie_node().child_count == 0
    }

    /// Return an iterator over the keys and values of the Trie.
    fn iter(self) -> Iter<'a, V> {
        Iter::new(self.trie_node())
    }

    /// Return an iterator over the keys of the Trie.
    fn keys(self) -> Keys<'a, V> {
        Keys::new(self.iter())
    }

    /// Return an iterator over the values of the Trie.
    fn values(self) -> Values<'a, V> {
        Values::new(self.iter())
    }

    /// Return an iterator over the child subtries of this node.
    fn children(self) -> Children<'a, V>;

    /// Get the prefix of this node.
    fn prefix(self) -> &'a NibbleVec {
        &self.trie_node().key
    }
}

/// Helper trait for Trie/SubTrie/SubTrieMut, which all contain a trie node.
pub trait ContainsTrieNode<'a, V: 'a> {
    fn trie_node(self) -> &'a TrieNode<V>;
}

/// Regular trie.
impl<'a, V: 'a> ContainsTrieNode<'a, V> for &'a Trie<V> {
    fn trie_node(self) -> &'a TrieNode<V> {
        &self.node
    }
}

impl<'a, V: 'a> TrieCommon<'a, V> for &'a Trie<V> {
    fn len(self) -> usize {
        self.length
    }

    fn children(self) -> Children<'a, V> {
        Children::new(self.node.key.clone(), &self.node)
    }
}

/// Subtrie.
impl<'a: 'b, 'b, V: 'a> ContainsTrieNode<'a, V> for &'b SubTrie<'a, V> {
    fn trie_node(self) -> &'a TrieNode<V> {
        self.node
    }
}

impl<'a: 'b, 'b, V: 'a> TrieCommon<'a, V> for &'b SubTrie<'a, V> {
    fn len(self) -> usize {
        self.node.compute_size()
    }

    fn children(self) -> Children<'a, V> {
        Children::new(self.prefix.clone(), self.node)
    }
}

/// Mutable subtrie *by value* (consumes the subtrie).
impl<'a, V: 'a> ContainsTrieNode<'a, V> for SubTrieMut<'a, V> {
    fn trie_node(self) -> &'a TrieNode<V> {
        self.node
    }
}

impl<'a, V: 'a> TrieCommon<'a, V> for SubTrieMut<'a, V> {
    /// **Computes** from scratch.
    fn len(self) -> usize {
        self.node.compute_size()
    }

    fn children(self) -> Children<'a, V> {
        Children::new(self.prefix.clone(), self.node)
    }
}

/// Mutable subtrie *by reference* (doesn't consume the subtrie, but limited).
impl<'a: 'b, 'b, V: 'a> ContainsTrieNode<'b, V> for &'b SubTrieMut<'a, V> {
    fn trie_node(self) -> &'b TrieNode<V> {
        self.node
    }
}

impl<'a: 'b, 'b, V: 'a> TrieCommon<'b, V> for &'b SubTrieMut<'a, V> {
    fn len(self) -> usize {
        self.node.compute_size()
    }

    fn children(self) -> Children<'b, V> {
        Children::new(self.prefix.clone(), self.node)
    }
}
