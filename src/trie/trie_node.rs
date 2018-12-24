use std::ops::{Deref, DerefMut};
use std::default::Default;
use super::{NibbleVec, SubTrie, SubTrieMut, BRANCH_FACTOR};

#[derive(Debug)]
pub struct TrieNode<V> {
    /// Key fragments/bits associated with this node, such that joining the keys from all
    /// parent nodes and this node is equal to the bit-encoding of this node's key.
    pub key: NibbleVec,

    /// The value stored at this node.
    pub value: Option<Box<V>>,

    /// The number of children which are Some rather than None.
    pub child_count: usize,

    /// The children of this node stored such that the first nibble of each child key
    /// dictates the child's bucket.
    pub children: [Option<Box<TrieNode<V>>>; BRANCH_FACTOR],
}

macro_rules! no_children {
    () => {
        [
            None, None, None, None, None, None, None, None, None, None, None, None, None, None,
            None, None,
        ]
    };
}

impl<V> TrieNode<V> {
    /// Create a value-less, child-less TrieNode.
    pub fn new() -> TrieNode<V> {
        TrieNode {
            key: NibbleVec::new(),
            value: None,
            children: no_children![],
            child_count: 0,
        }
    }

    /// Create a TrieNode with no children.
    pub fn with_key_value(key_fragments: NibbleVec, value: V) -> TrieNode<V> {
        TrieNode {
            key: key_fragments,
            value: Some(Box::new(value)),
            children: no_children![],
            child_count: 0,
        }
    }

    /// Get the value stored at this node, if any.
    pub fn value(&self) -> Option<&V> {
        self.value.as_ref().map(|v| v.deref())
    }

    /// Get a mutable reference to the value stored at this node, if any.
    pub fn value_mut(&mut self) -> Option<&mut V> {
        self.value.as_mut().map(|v| v.deref_mut())
    }

    /// Compute the number of keys and values in this node's subtrie.
    pub fn compute_size(&self) -> usize {
        let mut size = if self.value.is_some() { 1 } else { 0 };

        for child in &self.children {
            if let Some(ref child) = *child {
                // TODO: could unroll this recursion
                size += child.compute_size();
            }
        }

        size
    }

    /// Add a child at the given index, given that none exists there already.
    pub fn add_child(&mut self, idx: usize, node: Box<TrieNode<V>>) {
        debug_assert!(self.children[idx].is_none());
        self.child_count += 1;
        self.children[idx] = Some(node);
    }

    /// Remove a child at the given index, if it exists.
    pub fn take_child(&mut self, idx: usize) -> Option<Box<TrieNode<V>>> {
        self.children[idx].take().map(|node| {
            self.child_count -= 1;
            node
        })
    }

    /// Helper function for removing the single child of a node.
    pub fn take_only_child(&mut self) -> Box<TrieNode<V>> {
        debug_assert_eq!(self.child_count, 1);
        for i in 0..BRANCH_FACTOR {
            if let Some(child) = self.take_child(i) {
                return child;
            }
        }
        unreachable!("node with child_count 1 has no actual children");
    }

    /// Set the value of a node, given that it currently lacks one.
    pub fn add_value(&mut self, value: V) {
        debug_assert!(self.value.is_none());
        self.value = Some(Box::new(value));
    }

    /// Move the value out of a node.
    pub fn take_value(&mut self) -> Option<V> {
        self.value.take().map(|v| *v)
    }

    /// Replace a value, returning the previous value if there was one.
    pub fn replace_value(&mut self, value: V) -> Option<V> {
        // TODO: optimise this?
        let previous = self.take_value();
        self.add_value(value);
        previous
    }

    /// Get a reference to this node if it has a value.
    pub fn as_value_node(&self) -> Option<&TrieNode<V>> {
        self.value.as_ref().map(|_| self)
    }

    /// Split a node at a given index in its key, transforming it into a prefix node of its
    /// previous self.
    pub fn split(&mut self, idx: usize) {
        // Extract all the parts of the suffix node, starting with the key.
        let key = self.key.split(idx);

        // Key-value.
        let value = self.value.take();

        // Children.
        let mut children = no_children![];

        for (i, child) in self.children.iter_mut().enumerate() {
            if child.is_some() {
                children[i] = child.take();
            }
        }

        // Child count.
        let child_count = self.child_count;
        self.child_count = 1;

        // Insert the collected items below what is now an empty prefix node.
        let bucket = key.get(0) as usize;
        self.children[bucket] = Some(Box::new(TrieNode {
            key: key,
            value: value,
            children: children,
            child_count: child_count,
        }));
    }

    pub fn as_subtrie(&self, prefix: NibbleVec) -> SubTrie<V> {
        SubTrie {
            prefix: prefix,
            node: self,
        }
    }

    pub fn as_subtrie_mut<'a>(
        &'a mut self,
        prefix: NibbleVec,
        length: &'a mut usize,
    ) -> SubTrieMut<'a, V> {
        SubTrieMut {
            prefix: prefix,
            length: length,
            node: self,
        }
    }

    /// Check the integrity of a trie subtree (quite costly).
    /// Return true and the size of the subtree if all checks are successful,
    /// or false and a junk value if any test fails.
    pub fn check_integrity_recursive(&self, depth: usize) -> (bool, usize) {
        let mut sub_tree_size = 0;
        let is_root = depth == 0;

        // Check that no value-less, non-root nodes have only 1 child.
        if !is_root && self.child_count == 1 && self.value.is_none() {
            println!("Value-less node with a single child.");
            return (false, sub_tree_size);
        }

        // Check that all non-root key vector's have length > 1.
        if !is_root && self.key.len() == 0 {
            println!("Key length is 0 at non-root node.");
            return (false, sub_tree_size);
        }

        // Check that the child count matches the actual number of children.
        let child_count = self
            .children
            .iter()
            .fold(0, |acc, e| acc + (e.is_some() as usize));

        if child_count != self.child_count {
            println!(
                "Child count error, recorded: {}, actual: {}",
                self.child_count, child_count
            );
            return (false, sub_tree_size);
        }

        // Compute the depth of the children of this node.
        let child_depth = depth + self.key.len();

        // Account for this node in the size check.
        if self.value.is_some() {
            sub_tree_size += 1;
        }

        // Recursively check children.
        for i in 0..BRANCH_FACTOR {
            if let Some(ref child) = self.children[i] {
                match child.check_integrity_recursive(child_depth) {
                    (false, _) => return (false, sub_tree_size),
                    (true, child_size) => sub_tree_size += child_size,
                }
            }
        }

        (true, sub_tree_size)
    }
}

impl<V> Default for TrieNode<V> {
    fn default() -> Self {
        Self::new()
    }
}
