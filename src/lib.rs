//! An implementation of a set and a map using a pair of sparse and dense arrays as backing stores,
//! based on the paper "An efficient representation for sparse sets" (1993) by Briggs and Torczon.
//!
//! This type of set is useful when you need to efficiently track set membership for integers
//! from a large universe, but the values are relatively spread apart.
//!
//! Compared to the standard library's `HashSet`, clearing a set is O(1) instead of O(n).
//! Compared to a bitmap-based set, iteration over the set is
//! proportional to the cardinality of the set (how many elements you have) instead of proportional to the maximum size of the set.
//!
//! The main downside is that the set uses more memory than other set implementations. Its ideal usage is in
//! scenarios where the same set(s) can be reused many times (e.g. by using the `clear` operation).
//!
//! The map behaves identically to the set with the exception that it tracks data alongside
//! the values that are stored in the set. Under the hood, `SparseSet` is a `SparseMap` of keys to `()`.
//!
//! The table below compares the asymptotic complexities of several set operations for the sparse set when compared a bit set.
//! `n` is the number of elements in the set and `u` is the size of the set's universe.
//!
//! | Operation | Sparse Set | Bit Set |
//! | --------- | ---------- | ------- |
//! | Insertion | O(1)       | O(1)    |
//! | Removal   | O(1)       | O(1)    |
//! | Lookup    | O(1)       | O(1)    |
//! | Clear     | O(1)       | O(u)    |
//! | Count     | O(1)       | O(u)    |
//! | Iteration | O(n)       | O(u)    |
//! | Union     | O(n)       | O(u)    |
//! | Intersection | O(n)    | O(u)    |
//! | Difference | O(n)      | O(u)    |
//! | Complement | O(n)      | O(u)    |
//!
//! # Benchmarks
//!
//! The following benchmarks were run on a 2020 MacBook Pro with a 2 GHz Intel Core i5 processor.
//!
//! The benchmark compares `SparseSet` to the standard library's `HashSet` and the `bit-set` crate's `BitSet`.
//! It assumes the set is being reused by the program and new sets do not need to be created often.
//!
//! When inserting 1000 random elements into the set from a universe of [0, 2^16) iterating over the set, and clearing it,
//! the sparse set is **1.7** faster than the `HashSet` and **1.6x** faster than the `BitSet`:
//!
//! - `SparseSet`: 9,574 ns/iter (+/- 87)
//! - `BitSet`: 15,318 ns/iter (+/- 171)
//! - `HashSet`: 16,613 ns/iter (+/- 311)
//!
//! Benchmarks are available in examples/bench.rs and can be run with the following command:
//!
//! ```bash
//! cargo run --example bench --release
//! ```
//!
//! # Examples
//!
//! ```
//! use thinset::SparseSet;
//!
//! let mut s: SparseSet<usize> = SparseSet::new();
//! s.insert(0);
//! s.insert(3);
//! s.insert(7);
//!
//! s.remove(7);
//!
//! if !s.contains(7) {
//!     println!("There is no 7");
//! }
//!
//! // Print 0, 1, 3 in some order
//! for x in s.iter() {
//!     println!("{}", x);
//! }
//! ```
//!
//! ```
//! use thinset::{Pair, SparseMap};
//!
//! let mut m: SparseMap<u32, u32> = SparseMap::new();
//!
//! m.insert(13, 2);
//! m.insert(8, 16);
//!
//! assert_eq!(m.get(13), Some(&2));
//! assert_eq!(m.get(6), None);
//!
//! for Pair {key, value} in m.iter() {
//!     println!("{key}:{value}");
//! }
//! ```

use core::fmt;
use core::fmt::Debug;

use num_traits::PrimInt;
use num_traits::Unsigned;

/// A pair stored in the map. Mostly used for readability advantages over (,).
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Pair<K, V> {
    pub key: K,
    pub value: V,
}

impl<K, V> Pair<K, V> {
    fn new(key: K, value: V) -> Self {
        Pair { key, value }
    }
}

/// A sparse map of unsigned integer keys to values.
pub struct SparseMap<K: PrimInt + Unsigned, V> {
    cap: usize,
    sparse: Vec<usize>,
    dense: Vec<Pair<K, V>>,
}

impl<K: PrimInt + Unsigned, V> SparseMap<K, V> {
    /// Creates an empty SparseMap.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::SparseMap;
    ///
    /// let map: SparseMap<u32, u32> = SparseMap::new();
    /// assert!(map.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::with_capacity(0x1000)
    }

    /// Creates an empty SparseMap that's allocated to store elements
    /// with keys up to `cap - 1`. If bigger keys get inserted, the
    /// map grows automatically.
    ///
    /// If `cap` is greater than the largest number of unique `K`s, then the capacity
    /// of the map is decreased to only hold exactly the largest number of unique `K`s.
    /// For example, if `K` is `u8` and the capacity `10000` is given, only `255`
    /// elements will be allocated, because it's impossible for a set of `u8`s to hold
    /// any more elements than `255`.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::SparseMap;
    ///
    /// let mut map: SparseMap<u8, u32> = SparseMap::with_capacity(100);
    /// assert!(map.is_empty());
    ///
    /// // The map's initial capacity is 100, but it can grow to hold more elements.
    /// for i in 0..200 {
    ///    map.insert(i, 0);
    /// }
    /// assert_eq!(map.len(), 200);
    /// ```
    #[allow(clippy::uninit_vec)]
    pub fn with_capacity(cap: usize) -> Self {
        // If the system's size allows it, `max_cap` is big enough to hold all unique `K`s.
        let max_cap = K::max_value()
            .to_usize()
            .unwrap_or(usize::MAX)
            .saturating_add(1);
        let cap = cap.min(max_cap);

        // Allocate a vec of `cap` zeroed elements. In the original paper, the `sparse`
        // array would be left uninitialized, and the algorithm would work with garbage
        // values from memory. However, in Rust it's never safe to access uninitialized
        // memory [1], so we must zero the array to avoid undefined behavior.
        //
        // [1]: https://www.ralfj.de/blog/2019/07/14/uninit.html
        let sparse = vec![0; cap];

        Self {
            cap,
            sparse,
            dense: Vec::new(),
        }
    }

    /// Returns true if the map contains the key.
    ///
    /// # Panics
    ///
    /// If `key` cannot be cast to `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{map, SparseMap};
    ///
    /// let map: SparseMap<u32, u32> = map![(0, 1), (1, 2), (2, 3)];
    /// assert!(map.contains(1));
    /// assert!(!map.contains(3));
    /// ```
    pub fn contains(&self, key: K) -> bool {
        let ukey = key.to_usize().unwrap();
        if ukey >= self.cap {
            return false;
        }

        let r = self.sparse[ukey];

        r < self.dense.len() && self.dense[r].key == key
    }

    /// Inserts `value` into the map behind `key`.
    ///
    /// Returns whether the key-value pair was newly inserted. This is:
    /// - `true` if the key didn't exist before.
    /// - `false` if the key did exist, and an old value was overwritten.
    ///
    /// # Panics
    ///
    /// If `key` cannot be cast to `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{map, SparseMap};
    ///
    /// let mut map: SparseMap<u32, u32> = map![(0, 1), (1, 2), (2, 3)];
    /// assert_eq!(map.insert(1, 4), false);
    /// assert_eq!(map.insert(3, 4), true);
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> bool {
        let ukey = key.to_usize().unwrap();
        if ukey >= self.cap {
            self.grow_to_max(ukey);
        }

        let r = self.sparse[ukey];

        // Overwrite the value if the key is already present.
        if r < self.dense.len() && self.dense[r].key == key {
            self.dense[r].value = value;
            return false;
        }

        self.sparse[ukey] = self.dense.len();
        self.dense.push(Pair::new(key, value));

        true
    }

    fn grow_to_max(&mut self, new_max: usize) {
        let cap = new_max
            .checked_add(1)
            .expect("maximum key is greater than the maximum allowed by the system's usize");
        self.sparse
            .extend(std::iter::repeat(0).take(cap - self.cap));

        self.cap = cap;
    }

    /// Get the value behind the given `key`. Returns `None` if the key doesn't exist.
    ///
    /// # Panics
    ///
    /// If `key` cannot be cast to `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{map, SparseMap};
    ///
    /// let map: SparseMap<u32, u32> = map![(0, 1), (1, 2), (2, 3)];
    /// assert_eq!(map.get(1), Some(&2));
    /// assert_eq!(map.get(3), None);
    /// ```
    pub fn get(&self, key: K) -> Option<&V> {
        let ukey = key.to_usize().unwrap();
        if ukey >= self.cap {
            return None;
        }

        let r = self.sparse[ukey];
        if r < self.dense.len() && self.dense[r].key == key {
            return Some(&self.dense[r].value);
        }

        None
    }

    /// Get mutable access to the value behind the given `key`.
    /// Returns `None` if the key doesn't exist.
    ///
    /// # Panics
    ///
    /// If `key` cannot be cast to `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{map, SparseMap};
    ///
    /// let mut map: SparseMap<u32, u32> = map![(0, 1), (1, 2), (2, 3)];
    /// assert_eq!(map.get_mut(1), Some(&mut 2));
    /// assert_eq!(map.get_mut(3), None);
    /// ```
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        let ukey = key.to_usize().unwrap();
        if ukey >= self.cap {
            return None;
        }

        let r = self.sparse[ukey];
        if r < self.dense.len() && self.dense[r].key == key {
            return Some(&mut self.dense[r].value);
        }

        None
    }

    /// Updates the value behind `key` with `f` or inserts
    /// `value` if `key` doesn't exist.
    ///
    /// Returns whether `key` existed and `f` was used to update
    /// the existing value. That is
    /// - `true` if `f` was applied and used to update a value.
    /// - `false` if `default` was inserted an `f` was never run.
    ///
    /// # Panics
    ///
    /// If `key` cannot be cast to `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{map, SparseMap};
    ///
    /// let mut map: SparseMap<u32, u32> = map![(0, 1), (1, 2), (2, 3)];
    /// assert_eq!(map.update(1, |n| n * 2, 0), true);
    /// assert_eq!(map.update(3, |n| n * 2, 0), false);
    /// ```
    pub fn update<F>(&mut self, key: K, f: F, default: V) -> bool
    where
        F: Fn(&V) -> V,
    {
        let ukey = key.to_usize().unwrap();
        if ukey >= self.cap {
            self.insert(key, default);
            return false;
        }

        let r = self.sparse[ukey];
        if r < self.dense.len() && self.dense[r].key == key {
            self.dense[r].value = f(&self.dense[r].value);
            true
        } else {
            self.insert(key, default);
            false
        }
    }

    /// Removes a key-value pair from the map. Returns the value if the key was previously in the map.
    ///
    /// # Panics
    ///
    /// If `key` cannot be cast to `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{map, SparseMap};
    ///
    /// let mut map: SparseMap<u32, u32> = map![(0, 1), (1, 2), (2, 3)];
    /// assert_eq!(map.remove(1), Some(2));
    /// assert_eq!(map.remove(1), None);
    /// ```
    pub fn remove(&mut self, key: K) -> Option<V> {
        let ukey = key.to_usize().unwrap();
        if ukey >= self.cap {
            return None;
        }

        let r = self.sparse[ukey];

        // Remove only if the pair is part of the map.
        if r < self.dense.len() && self.dense[r].key == key {
            // Remove the pair by giving its slot to the last pair in `dense`.
            // First, update the last pair's slot in `sparse` to point to where the last pair's new location will be.
            self.sparse[self.dense.last().unwrap().key.to_usize().unwrap()] = r;

            // Then, swap the pair we're removing with the last pair in `dense`, and remove the last pair.
            // For example, if `dense` was [A, B, C] and we were removing A, we'd swap A with C and remove C,
            // leaving [C, B].
            let removed_pair = self.dense.swap_remove(r);

            return Some(removed_pair.value);
        }

        None
    }

    /// Returns true if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{map, SparseMap};
    ///
    /// let mut map: SparseMap<u32, u32> = map![(0, 1), (1, 2), (2, 3)];
    /// assert!(!map.is_empty());
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.dense.is_empty()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{map, SparseMap};
    ///
    /// let mut map: SparseMap<u32, u32> = map![(0, 1), (1, 2), (2, 3)];
    /// assert_eq!(map.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.dense.len()
    }

    /// Removes all elements from the map.
    ///
    /// This operation is O(1). It does not deallocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{map, SparseMap};
    ///
    /// let mut map: SparseMap<u32, u32> = map![(0, 1), (1, 2), (2, 3)];
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        // The dense array contains pairs of integers, so no destructors need to be called.
        self.dense.clear();
    }

    /// An iterator visiting all elements in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{map, Pair, SparseMap};
    ///
    /// let mut map: SparseMap<u32, u32> = map![(0, 1), (1, 2), (2, 3)];
    ///
    /// // Print 0:1, 1:2, 2:3 in arbitrary order
    /// for Pair {key, value} in map.iter() {
    ///    println!("{key}:{value}");
    /// }
    /// ```
    pub fn iter(&self) -> SparseMapIter<'_, K, V> {
        SparseMapIter(self.dense.iter())
    }
}

impl<K: PrimInt + Unsigned + Debug, V: Debug> Debug for SparseMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut d = f.debug_map();
        for pair in &self.dense {
            d.entry(&pair.key, &pair.value);
        }
        d.finish()
    }
}

impl<K: PrimInt + Unsigned, V: PartialEq> PartialEq for SparseMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        for pair in &self.dense {
            match other.get(pair.key) {
                Some(value) => {
                    if value != &pair.value {
                        return false;
                    }
                }
                None => return false,
            }
        }

        true
    }
}

impl<K: PrimInt + Unsigned, V: Eq> Eq for SparseMap<K, V> {}

/// An iterator over the key-value pairs of a [`SparseMap`].
///
/// This struct is created by the [`iter`] method on [`SparseMap`].
///
/// [`iter`]: SparseMap::iter
#[derive(Clone)]
pub struct SparseMapIter<'a, K: PrimInt + Unsigned, V>(std::slice::Iter<'a, Pair<K, V>>);

impl<'a, K: PrimInt + Unsigned, V> Iterator for SparseMapIter<'a, K, V> {
    type Item = &'a Pair<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K: PrimInt + Unsigned, V: Clone> Clone for SparseMap<K, V> {
    fn clone(&self) -> Self {
        Self {
            cap: self.cap,
            sparse: self.sparse.clone(),
            dense: self.dense.clone(),
        }
    }
}

impl<K: PrimInt + Unsigned, V> Default for SparseMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

// `IntoIterator` implementation for [`SparseMap`].
impl<K: PrimInt + Unsigned, V> IntoIterator for SparseMap<K, V> {
    type Item = Pair<K, V>;
    type IntoIter = SparseMapIntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        SparseMapIntoIter {
            iter: self.dense.into_iter(),
        }
    }
}

/// An owned iterator over the key-value pairs of a [`SparseMap`].
///
/// This struct is created by the [`into_iter`] method on [`SparseMap`].
///
/// [`into_iter`]: SparseMap::iter
#[derive(Clone)]
pub struct SparseMapIntoIter<K: PrimInt + Unsigned, V> {
    iter: std::vec::IntoIter<Pair<K, V>>,
}

impl<K: PrimInt + Unsigned, V> Iterator for SparseMapIntoIter<K, V> {
    type Item = Pair<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K: PrimInt + Unsigned, V> std::ops::Index<K> for SparseMap<K, V> {
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<K: PrimInt + Unsigned, V> std::ops::IndexMut<K> for SparseMap<K, V> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

/// A sparse set of integer values.
pub struct SparseSet<T: PrimInt + Unsigned> {
    inner: SparseMap<T, ()>,
}

impl<T: PrimInt + Unsigned> SparseSet<T> {
    /// Creates an empty SparseSet.
    pub fn new() -> Self {
        Self {
            inner: SparseMap::new(),
        }
    }

    /// Creates an empty SparseSet that's allocated to store elements
    /// with values up to `cap - 1`.
    ///
    /// See [`SparseMap`] for more info.
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            inner: SparseMap::with_capacity(cap),
        }
    }

    /// Returns true if the set contains a value.
    ///
    /// # Panics
    ///
    /// If `value` cannot be cast to `usize`.
    pub fn contains(&self, value: T) -> bool {
        self.inner.contains(value)
    }

    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    /// - `true` if the value didn't exist before.
    /// - `false` if the value did already exist.
    ///
    /// # Panics
    ///
    /// If `value` cannot be cast to `usize`.
    pub fn insert(&mut self, value: T) -> bool {
        self.inner.insert(value, ())
    }

    /// Removes a value from the set. Returns whether the value was present in the set.
    ///
    /// # Panics
    ///
    /// If `value` cannot be cast to `usize`.
    pub fn remove(&mut self, value: T) -> bool {
        self.inner.remove(value).is_some()
    }

    /// Returns true if the set contains no elements.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns the number of elements in the set.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Removes all elements from the set.
    ///
    /// This operation is O(1). It does not deallocate memory.
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// An iterator visiting all elements in arbitrary order.
    pub fn iter(&self) -> SparseSetIter<T> {
        SparseSetIter {
            iter: self.inner.iter(),
        }
    }

    /// Return `true` if `self` (A) is an improper subset of `other` (B):
    ///
    /// A ⊆ B.
    ///
    /// This is the same as [`Self::is_superset`] with the arguments flipped.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{set, SparseSet};
    ///
    /// let a: SparseSet<u64> = set![6, 3, 5, 64, 2];
    /// let b = {
    ///     let mut b = a.clone();
    ///     b.insert(14);
    ///     b
    /// };
    ///
    /// // `b` contains all elements that `a` contains.
    /// assert!(a.is_subset(&b) && b.is_superset(&a));
    /// // `a` != `b`, so `a` is a proper subset of `b`.
    /// assert!(a.is_proper_subset(&b));
    /// ```
    pub fn is_subset(&self, other: &Self) -> bool {
        for x in self.iter() {
            if !other.contains(x) {
                return false;
            }
        }

        true
    }

    /// Return `true` if `self` (A) is an improper superset of `other` (B):
    ///
    /// A ⊇ B.
    ///
    /// This is the same as [`Self::is_subset`] with the arguments flipped.
    pub fn is_superset(&self, other: &Self) -> bool {
        for x in other.iter() {
            if !self.contains(x) {
                return false;
            }
        }

        true
    }

    /// Return `true` if `self` (A) is a proper subset of `other` (B):
    ///
    /// A ⊊ B.
    ///
    /// This is the same as [`Self::is_proper_superset`] with the arguments flipped.
    pub fn is_proper_subset(&self, other: &Self) -> bool {
        self.inner.len() < other.inner.len() && self.is_subset(other)
    }

    /// Return `true` if `self` (A) is a proper superset of `other` (B):
    ///
    /// A ⊋ B.
    ///
    /// This is the same as [`Self::is_proper_subset`] with the arguments flipped.
    pub fn is_proper_superset(&self, other: &Self) -> bool {
        self.inner.len() > other.inner.len() && self.is_superset(other)
    }

    /// Return `true` if `self` (A) and `other` (B) are disjoint:
    ///
    /// A ∩ B = ∅.
    pub fn is_disjoint(&self, other: &Self) -> bool {
        for x in self.iter() {
            if other.contains(x) {
                return false;
            }
        }

        true
    }

    /// Iterator over each element stored in `self` union `other`.
    /// This constructs a new sparse set internally.
    /// See [union_with](#method.union_with) for an efficient in-place version.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{set, SparseSet};
    ///
    /// let a: SparseSet<usize> = set![1, 2, 4];
    /// let b: SparseSet<usize> = set![0, 2];
    ///
    /// // Print 0, 1, 2, 4 in arbitrary order
    /// for x in a.union(&b) {
    ///     println!("{}", x);
    /// }
    /// ```
    pub fn union<'a>(&'a self, other: &'a Self) -> Union<T, UnionIter<'a, T>> {
        Union {
            u: SparseSet::new(),
            i: self.iter().chain(other.iter()),
        }
    }

    /// Unions in-place with the specified other set.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{set, SparseSet};
    ///
    /// let mut a: SparseSet<usize> = set![1, 2, 4];
    /// let b: SparseSet<usize> = set![0, 2];
    /// let res: SparseSet<usize> = set![0, 1, 2, 4];
    ///
    /// a.union_with(&b);
    /// assert_eq!(a, res);
    /// ```
    pub fn union_with(&mut self, other: &Self) {
        for value in other.iter() {
            self.insert(value);
        }
    }

    /// Iterator over the union of all sets in the given iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{set, SparseSet};
    ///
    /// let s = vec![set![1, 2, 3], set![2, 3, 4], set![3, 4, 5]];
    /// let u = SparseSet::union_all(s.iter()).collect::<SparseSet<u8>>();
    ///
    /// assert_eq!(u, set![5, 1, 3, 4, 2]);
    /// ```
    pub fn union_all<'a, I: Iterator<Item = &'a Self>>(i: I) -> Union<T, UnionAllIter<'a, I, T>> {
        Union {
            u: SparseSet::new(),
            i: i.flat_map(Self::iter),
        }
    }
}

impl<T: PrimInt + Unsigned> Clone for SparseSet<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T: PrimInt + Unsigned> Default for SparseSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: PrimInt + Unsigned + Debug> Debug for SparseSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut d = f.debug_set();
        for pair in &self.inner.dense {
            d.entry(&pair.key);
        }
        d.finish()
    }
}

impl<T: PrimInt + Unsigned> PartialEq for SparseSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<T: PrimInt + Unsigned> Eq for SparseSet<T> {}

/// An iterator over the elements of a `SparseSet`.
///
/// This struct is created by the [`iter`] method on [`SparseSet`].
///
/// [`iter`]: SparseSet::iter
#[derive(Clone)]
pub struct SparseSetIter<'a, T: PrimInt + Unsigned> {
    iter: SparseMapIter<'a, T, ()>,
}

impl<'a, T: PrimInt + Unsigned> Iterator for SparseSetIter<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|Pair { key, value: _ }| *key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T: PrimInt + Unsigned> IntoIterator for SparseSet<T> {
    type Item = T;
    type IntoIter = SparseSetIntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        SparseSetIntoIter {
            iter: self.inner.into_iter(),
        }
    }
}

/// An owned iterator over the elements of a [`SparseSet`].
///
/// This struct is created by the [`into_iter`] method on [`SparseSet`].
///
/// [`into_iter`]: SparseSet::into_iter
#[derive(Clone)]
pub struct SparseSetIntoIter<T: PrimInt + Unsigned> {
    iter: SparseMapIntoIter<T, ()>,
}

impl<T: PrimInt + Unsigned> Iterator for SparseSetIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|Pair { key, value: _ }| key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T: PrimInt + Unsigned> FromIterator<T> for SparseSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut s = SparseSet::new();

        for x in iter {
            s.insert(x);
        }

        s
    }
}

#[derive(Clone)]
pub struct Union<T: PrimInt + Unsigned, I: Iterator<Item = T>> {
    u: SparseSet<T>,
    i: I,
}

impl<T: PrimInt + Unsigned, I: Iterator<Item = T>> Iterator for Union<T, I> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.i.by_ref().find(|&x| self.u.insert(x))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.i.size_hint()
    }
}

type UnionIter<'a, T> = core::iter::Chain<SparseSetIter<'a, T>, SparseSetIter<'a, T>>;
type UnionAllIter<'a, I, T> =
    core::iter::FlatMap<I, SparseSetIter<'a, T>, fn(&'a SparseSet<T>) -> SparseSetIter<'a, T>>;

/// A macro to create and initialize maps in one go.
/// ```rust
/// use thinset::{map, SparseMap};
/// let mut map: SparseMap<u32, u32> = map![(4, 0), (32, 1), (16, 2), (24, 3), (63, 4)];
/// assert_eq!(map.get(32), Some(&1));
/// assert_eq!(map.get(63), Some(&4));
/// map.update(32, |n| n * 2, 0);
/// assert_eq!(map.get(32), Some(&2));
/// ```
#[macro_export]
macro_rules! map {
    () => (
        $crate::SparseMap::new()
    );
    ($($x:expr),+ $(,)?) => (
        {
            let mut m = $crate::SparseMap::new();
            $(
                m.insert($x.0, $x.1);
            )+
            m
        }
    );
}

/// A macro to create and initialize sets in one go.
///
/// ```rust
/// use thinset::{set, SparseSet};
/// let mut set: SparseSet<u32> = set![4, 32, 16, 24, 63];
/// assert!(set.contains(32));
/// assert!(set.contains(63));
/// set.insert(25);
/// ```
#[macro_export]
macro_rules! set {
    () => (
        $crate::SparseSet::new()
    );
    ($($x:expr),+ $(,)?) => (
        {
            let mut s = $crate::SparseSet::new();
            $(
                s.insert($x);
            )+
            s
        }
    );
}

/// Check if `self` is an element of a given set.
/// See [`InSet::is_in`] for more information.
pub trait InSet {
    type Set;

    /// Return true if `self` (x) is an element of `set` (A):
    ///
    /// x ∈ A.
    ///
    /// # Examples
    ///
    /// ```
    /// use thinset::{set, SparseSet, InSet};
    ///
    /// let s: SparseSet<u16> = set![5, 4, 15, 3, 91];
    /// if 5.is_in(&s) {
    ///     println!("5 is an element of s");
    /// }
    /// ```
    fn is_in(&self, set: &Self::Set) -> bool;
}

impl<T: PrimInt + Unsigned> InSet for T {
    type Set = SparseSet<T>;

    fn is_in(&self, set: &Self::Set) -> bool {
        set.contains(*self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::Rng;

    #[test]
    fn sparse_map_example() {
        let map: SparseMap<usize, usize> = SparseMap::with_capacity(50);
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);

        assert!(!map.contains(0));
        assert!(!map.contains(42));
        assert!(!map.contains(5));

        let mut map = map;
        map.insert(0, 1);
        map.insert(41, 2);

        assert!(!map.is_empty());
        assert_eq!(map.len(), 2);
        assert!(map.contains(0));
        assert!(map.contains(41));
        assert!(!map.contains(14));
        assert_eq!(map.get(0), Some(&1));
        assert_eq!(map.get(41), Some(&2));
        assert_eq!(map.get(14), None);

        map.update(41, |n| n * n, 0);
        assert_eq!(map.get(41), Some(&4));
        map.update(14, |n| *n, 10);
        assert_eq!(map.get(14), Some(&10));

        map.clear();

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn sparse_map_has_default_impl() {
        let mut set: SparseMap<u32, i32> = Default::default();
        set.insert(4, 2);
        assert!(set.contains(4));
    }

    #[test]
    fn sparse_map_iter() {
        let mut map: SparseMap<u32, i32> = SparseMap::new();
        map.insert(4, 5);
        map.insert(6, 7);
        map.insert(9, 10);

        let mut iter = map.iter();
        assert_eq!(iter.next(), Some(&Pair::new(4, 5)));
        assert_eq!(iter.next(), Some(&Pair::new(6, 7)));
        assert_eq!(iter.next(), Some(&Pair::new(9, 10)));
        assert_eq!(iter.next(), None);

        map.remove(9);
        let mut iter = map.iter();
        assert_eq!(iter.next(), Some(&Pair::new(4, 5)));
        assert_eq!(iter.next(), Some(&Pair::new(6, 7)));
        assert_eq!(iter.next(), None);

        map.remove(6);
        map.remove(4);
        let mut iter = map.iter();
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn sparse_map_into_iter() {
        let mut map: SparseMap<u64, i64> = SparseMap::with_capacity(100);
        map.insert(5, 1000);
        map.insert(6, 572);
        map.insert(7, 8);

        let mut iter = map.into_iter();
        // Note there are no references here.
        assert_eq!(iter.next(), Some(Pair::new(5, 1000)));
        assert_eq!(iter.next(), Some(Pair::new(6, 572)));
        assert_eq!(iter.next(), Some(Pair::new(7, 8)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn sparse_map_contains_key_out_of_bounds() {
        let map: SparseMap<usize, i32> = SparseMap::new();
        assert_eq!(map.len(), 0);
        assert!(!map.contains(4000));
        assert!(!map.contains(0));
        assert!(!map.contains(10));
    }

    #[test]
    fn sparse_map_grows_as_needed() {
        let mut m: SparseMap<u32, u32> = SparseMap::with_capacity(20);
        assert!(m.insert(390, 0));
        assert!(m.contains(390));
        assert!(m.insert(200, 10));
        assert!(m.contains(200));
        assert_eq!(m.remove(390), Some(0));
        assert_eq!(m.remove(200), Some(10));
    }

    #[test]
    fn sparse_map_insert_random_values() {
        let mut rng = rand::thread_rng();
        let size = rng.gen_range(0x100..0x1000);

        let k = gen_random_vec(size);
        let v = gen_random_vec(size);
        let mut m: SparseMap<u32, u32> = SparseMap::new();

        // Check that inserting random values works.
        for (&k, &v) in k.iter().zip(v.iter()) {
            m.insert(k, v);
        }

        // Check that all of the inserted values are actually inserted.
        for &k in k.iter() {
            assert!(m.contains(k));
        }

        // After removing every element at least once, the map should be empty.
        // `k` can contain duplicates, so the same value might be removed
        // more than once.
        for &k in &k {
            m.remove(k);
        }
        assert!(m.is_empty());
    }

    #[test]
    #[should_panic]
    fn sparse_map_key_must_fit_usize() {
        let map: SparseMap<u128, i32> = SparseMap::new();
        map.contains(usize::MAX as u128 + 1);
    }

    #[test]
    fn sparse_map_can_be_indexed() {
        let mut map: SparseMap<u32, i32> = SparseMap::new();
        map.insert(10, 100);
        map.insert(5, 50);
        assert_eq!(map[10], 100);
        assert_eq!(map[5], 50);
    }

    #[test]
    #[should_panic]
    fn sprase_map_index_out_of_range() {
        let mut map: SparseMap<u32, i32> = SparseMap::new();
        map.insert(4, 5);
        let _ = map[5];
    }

    #[test]
    fn sparse_map_can_be_indexed_mutably() {
        let mut map: SparseMap<u32, i32> = SparseMap::new();
        map.insert(6, 10);
        assert_eq!(map.get(6), Some(&10));
        map[6] = 5;
        assert_eq!(map.get(6), Some(&5));
        let x = &mut map[6];
        *x = 7;
        *x += 1;
        assert_eq!(map.get(6), Some(&8));
    }

    #[test]
    #[should_panic]
    fn sparse_map_mutable_index_out_of_range() {
        let mut map: SparseMap<u32, i32> = SparseMap::new();
        map.insert(51, 0);
        let x: &mut i32 = &mut map[53];
        *x = 60;
    }

    #[test]
    fn sparse_map_debug_impl() {
        let mut map: SparseMap<u32, i32> = SparseMap::new();
        map.insert(4, 5);
        map.insert(6, 7);
        map.insert(9, 10);
        assert_eq!(format!("{:?}", map), "{4: 5, 6: 7, 9: 10}");
    }

    #[test]
    fn sparse_map_eq() {
        let mut map1: SparseMap<u32, i32> = SparseMap::new();
        let mut map2: SparseMap<u32, i32> = SparseMap::new();
        assert_eq!(map1, map2);

        map1.insert(1, 2);
        assert_ne!(map1, map2);

        map2.insert(1, 2);
        assert_eq!(map1, map2);

        map1.insert(3, 4);
        assert_ne!(map1, map2);

        map2.insert(3, 5);
        assert_ne!(map1, map2);
    }

    #[test]
    fn sparse_map_partial_eq() {
        let mut map1: SparseMap<u32, f64> = SparseMap::new();
        let mut map2: SparseMap<u32, f64> = SparseMap::new();
        assert_eq!(map1, map2);

        map1.insert(1, 2.0);
        assert_ne!(map1, map2);

        map2.insert(1, 2.0);
        assert_eq!(map1, map2);

        map1.insert(3, f64::NAN);
        assert_ne!(map1, map2);

        map2.insert(3, f64::NAN);
        assert_ne!(map1, map2);
    }

    #[test]
    fn sparse_map_non_copy_data() {
        let mut map: SparseMap<u32, String> = SparseMap::new();
        map.insert(1, "hello".to_string());
        map.insert(2, "world".to_string());
        assert_eq!(map.get(1), Some(&"hello".to_string()));
        assert_eq!(map.get(2), Some(&"world".to_string()));

        map.update(1, |s| s.to_uppercase(), "foo".to_string());
        assert_eq!(map.get(1), Some(&"HELLO".to_string()));

        map.remove(1);
        assert_eq!(map.get(1), None);

        map.clear();
        assert!(map.is_empty());
    }

    #[test]
    fn sparse_set_unit_tuple_trick_works() {
        use std::mem::size_of;

        // `SparseSet` is a `SparseMap` of `Pair<K, ()>`s. On every insertion into
        // the map, such a pair is appended to the end of `dense`. This test asserts
        // that using the unit tuple trick to implement a set on top of a map uses
        // the same amount of memory as a direct implementation of the set would. The
        // same trick is employed by `std::collections::HashSet`.

        assert_eq!(size_of::<usize>(), size_of::<Pair<usize, ()>>());
        assert_eq!(size_of::<u128>(), size_of::<Pair<u128, ()>>());
        assert_eq!(size_of::<u64>(), size_of::<Pair<u64, ()>>());
        assert_eq!(size_of::<u32>(), size_of::<Pair<u32, ()>>());
        assert_eq!(size_of::<u16>(), size_of::<Pair<u16, ()>>());
        assert_eq!(size_of::<u8>(), size_of::<Pair<u8, ()>>());
    }

    #[test]
    fn sparse_set_example() {
        let set: SparseSet<usize> = SparseSet::with_capacity(50);
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);

        assert!(!set.contains(0));
        assert!(!set.contains(42));
        assert!(!set.contains(5));

        let mut set = set;
        set.insert(0);
        set.insert(42);

        assert!(!set.is_empty());
        assert_eq!(set.len(), 2);
        assert!(set.contains(0));
        assert!(set.contains(42));
        assert!(!set.contains(5));

        set.insert(5);
        set.insert(6);
        set.insert(7);
        set.remove(4); // no-op
        set.remove(5);
        set.remove(0);

        assert!(!set.is_empty());
        assert_eq!(set.len(), 3);
        assert!(!set.contains(0));
        assert!(set.contains(42));
        assert!(42.is_in(&set));
        assert!(!set.contains(5));
        assert!(set.contains(6));
        assert!(set.contains(7));

        set.clear();

        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn sparse_set_in() {
        let s: SparseSet<u8> = set![1, 2, 3, 4];
        assert!(1.is_in(&s));
        assert!(!6.is_in(&s));
        assert!(!u8::MAX.is_in(&s));
    }

    #[test]
    fn sparse_set_has_default_impl() {
        let mut set: SparseSet<u32> = Default::default();
        set.insert(4);
        assert!(set.contains(4));
    }

    #[test]
    fn sparse_set_macro_example() {
        {
            let mut set: SparseSet<u32> = set![1, 2, 3, 4, 5, 6, 6, 7, 7, 7];
            for i in 1..7 {
                assert!(set.contains(i));
            }
            set.insert(8);
            set.insert(1000);
            assert!(set.contains(8));
            assert!(set.contains(1000));
        }
        {
            let mut set: SparseSet<u32> = set![1, 2, 3, 54, 100];
            assert!(set.contains(1));
            assert!(set.contains(2));
            assert!(set.contains(3));
            assert!(set.contains(54));
            assert!(set.contains(100));
            set.remove(1);
            set.remove(2);
            set.remove(3);
            set.remove(54);
            set.remove(100);
            assert!(set.is_empty());
            assert!(!set.contains(1));
            assert!(!set.contains(2));
            assert!(!set.contains(3));
            assert!(!set.contains(54));
            assert!(!set.contains(100));
        }
        {
            let set: SparseSet<u8> = set![
                9, 10, 11, 100, // Note the trailing comma is allowed for visual uniformity.
            ];
            assert!(set.contains(100));
            assert!(set.contains(9));
            assert!(set.contains(10));
            assert!(set.contains(11));
        }
    }

    #[test]
    fn sparse_map_macro_example() {
        {
            let mut map: SparseMap<u32, u32> = map![
                (4, 0),
                (32, 1),
                (16, 2),
                (24, 3),
                (63, 4), // Trailing comma is allowed for visual uniformity.
            ];
            assert_eq!(map.get(32), Some(&1));
            assert_eq!(map.get(63), Some(&4));
            map.update(32, |n| n * 2, 0);
            assert_eq!(map.get(32), Some(&2));
        }
        {
            let mut map: SparseMap<u32, u32> = map![];
            assert_eq!(map.get(32), None);
            map.insert(32, 1);
            assert_eq!(map.get(32), Some(&1));
        }
    }

    #[test]
    fn sparse_set_iter() {
        let mut set: SparseSet<usize> = SparseSet::with_capacity(50);
        set.insert(3);
        set.insert(4);
        set.insert(5);

        let mut iter = set.iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), None);

        set.remove(4);

        let mut iter = set.iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), None);

        set.remove(3);
        set.remove(5);

        let mut iter = set.iter();
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn sparse_set_into_iter() {
        let mut set: SparseSet<usize> = SparseSet::with_capacity(50);
        set.insert(3);
        set.insert(4);
        set.insert(5);

        let mut iter = set.into_iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn sparse_set_contains_value_out_of_bounds() {
        let set: SparseSet<usize> = SparseSet::with_capacity(0);
        assert_eq!(set.len(), 0);
        assert!(!set.contains(0));
        assert!(!set.contains(100));
    }

    #[test]
    fn sparse_set_grows_as_needed() {
        let mut s: SparseSet<u32> = SparseSet::with_capacity(20);
        assert!(s.insert(100));
        assert!(s.contains(100));
        assert!(s.insert(200));
        assert!(s.contains(200));
        assert!(s.remove(100));
        assert!(s.remove(200));
    }

    #[test]
    fn sparse_set_insert_random_values() {
        let mut rng = rand::thread_rng();
        let r = gen_random_vec(rng.gen_range(0x100..0x1000));
        let mut s: SparseSet<u32> = SparseSet::new();

        // Check that inserting random values works.
        for &x in &r {
            s.insert(x);
        }

        // Check that all of the inserted values are actually inserted.
        for &x in &r {
            assert!(s.contains(x));
        }

        // After removing every element at least once, the set should be empty.
        // `r` can contain duplicates, so the same value might be removed
        // more than once.
        for &x in &r {
            s.remove(x);
        }
        assert!(s.is_empty());
    }

    #[test]
    fn sparse_set_debug_impl() {
        let mut set: SparseSet<u32> = SparseSet::new();
        set.insert(4);
        set.insert(6);
        set.insert(9);
        assert_eq!(format!("{:?}", set), "{4, 6, 9}");
    }

    #[test]
    fn sparse_set_eq() {
        let mut set1: SparseSet<u32> = SparseSet::new();
        let mut set2: SparseSet<u32> = SparseSet::new();
        assert_eq!(set1, set2);

        set1.insert(1);
        assert_ne!(set1, set2);

        set2.insert(1);
        assert_eq!(set1, set2);

        set1.insert(3);
        assert_ne!(set1, set2);

        set2.insert(4);
        assert_ne!(set1, set2);

        set1.insert(4);
        set2.insert(3);
        assert_eq!(set1, set2);
    }

    #[test]
    fn sparse_set_from_iter() {
        let s = vec![set![1, 2, 3], set![2, 3, 4], set![3, 4, 5]];
        let u = SparseSet::union_all(s.iter()).collect::<SparseSet<u8>>();

        assert_eq!(u, set![1, 2, 3, 4, 5]);
    }

    #[test]
    fn sparse_set_union() {
        let a: SparseSet<usize> = set![1, 2, 4];
        let b: SparseSet<usize> = set![0, 2];
        let res = a.union(&b);

        assert_eq!(res.size_hint(), (5, Some(5)));

        let expected: SparseSet<usize> = set![1, 2, 4, 0];
        assert_eq!(
            res.collect::<Vec<_>>(),
            expected.into_iter().collect::<Vec<_>>()
        );
    }

    #[test]
    fn sparse_set_unite_all() {
        let sets: Vec<SparseSet<u8>> = vec![set![1, 2, 3], set![5, 4, 3], set![9, 20, 18, 2]];
        let res = SparseSet::union_all(sets.iter());

        let expected: SparseSet<u8> = set![1, 2, 3, 5, 4, 9, 20, 18];
        assert_eq!(
            res.collect::<Vec<_>>(),
            expected.into_iter().collect::<Vec<_>>()
        );
    }

    #[test]
    fn sparse_set_union_with() {
        let mut a: SparseSet<usize> = set![1, 2, 4];
        let b: SparseSet<usize> = set![0, 2];
        let res: SparseSet<usize> = set![0, 1, 2, 4];

        a.union_with(&b);
        assert_eq!(a, res);
    }

    #[test]
    fn sparse_set_sub_and_super_sets() {
        let a: SparseSet<u32> = set![3, 4, 5];
        let b: SparseSet<u32> = set![2, 3, 4, 5, 6];
        assert!(a.is_subset(&b));
        assert!(b.is_superset(&a));
        assert!(a.is_proper_subset(&b));
        assert!(b.is_proper_superset(&a));

        let b = a.clone();
        assert!(a.is_subset(&b));
        assert!(b.is_superset(&a));
        assert!(!a.is_proper_subset(&b));
        assert!(!b.is_proper_superset(&a));
    }

    #[test]
    fn disjoint_sets() {
        let a: SparseSet<u32> = set![1, 2, 3, 4, 5];
        let b: SparseSet<u32> = set![6, 7, 8, 9, 10];
        assert!(a.is_disjoint(&b));
        assert!(b.is_disjoint(&a));

        let mut a = a;
        a.insert(6);
        assert!(!a.is_disjoint(&b));
        assert!(!b.is_disjoint(&a));
    }

    fn gen_random_vec(size: usize) -> Vec<u32> {
        let mut rng = rand::thread_rng();
        let mut vec = Vec::with_capacity(size);

        for _ in 0..size {
            vec.push(rng.gen_range(0..10000));
        }

        vec
    }
}
