//! An implementation of a set and a map using a pair of sparse and dense arrays as backing stores.
//!
//! This type of set is useful when you need to efficiently track set membership for integers
//! from a large universe, but the values are relatively spread apart.
//!
//! The sparse set supports constant-time insertion, removal, lookups as expected.
//! In addition:
//!
//! - Compared to the standard library's `HashSet`, clearing the set is constant-time instead of linear time.
//! - Compared to bitmap-based sets like the `bit-set` crate, iteration over the set is
//! proportional to the cardinality of the set (how many elements you have) instead of proportional to the maximum size of the set.
//!
//! The main downside is that the set requires more memory than other set implementations.
//!
//! The map behaves identically to the set with the exception that it tracks data alongside
//! the values that are stored in the set. Under the hood, `SparseSet` is a `SparseMap` of keys to `()`.
//!
//! The implementation is based on the paper "An efficient representation for sparse sets" (1993)
//! by Briggs and Torczon.
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
//! assert_eq!(m.get(13), Some(2));
//! assert_eq!(m.get(6), None);
//!
//! for Pair {key, value} in m.iter() {
//!     println!("{key}:{value}");
//! }
//! ```

use num_traits::PrimInt;
use num_traits::Unsigned;

/// A pair stored in the map. Mostly used for readability advantages over (,).
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Pair<K: PrimInt + Unsigned, V: Copy> {
    pub key: K,
    pub value: V,
}

impl<K: PrimInt + Unsigned, V: Copy> Pair<K, V> {
    fn new(key: K, value: V) -> Self {
        Pair { key, value }
    }
}

/// A sparse map of unsigned integer keys to integer values (or anything else that's copy).
pub struct SparseMap<K: PrimInt + Unsigned, V: Copy> {
    cap: usize,
    sparse: Vec<usize>,
    dense: Vec<Pair<K, V>>,
}

impl<K: PrimInt + Unsigned, V: Copy> SparseMap<K, V> {
    /// Creates an empty SparseMap.
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
    #[allow(clippy::uninit_vec)]
    pub fn with_capacity(cap: usize) -> Self {
        // If the system's size allows it, `max_cap` is big enough to hold all unique `K`s.
        let max_cap = K::max_value()
            .to_usize()
            .unwrap_or(usize::MAX)
            .saturating_add(1);
        let cap = cap.min(max_cap);

        // Allocate a vector size `cap` and initialize it with garbage values.
        // SAFETY: The call to `with_capacity(cap)` ensures that `set_len(cap)`
        // will succeed. `sparse` maybe be filled with garbage simply based on how
        // the map works. An element is only considered part of the map if the entires
        // in `dense` and `sparse` are linked correctly. Thus, memory in `sparse` must
        // not be initialized.
        let mut sparse = Vec::with_capacity(cap);
        unsafe {
            sparse.set_len(cap);
        }

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
        // SAFETY: The call to `reserve_exact(cap - self.sparse.len())` ensures that the capacity is
        // greater or equal to `cap` so that `set_len(cap)` will succeed. See `Self::with_capacity`
        // for more info on uninitialized memory in `sparse`.
        self.sparse.reserve_exact(cap - self.sparse.len());
        unsafe {
            self.sparse.set_len(cap);
        }

        self.cap = cap;
    }

    /// Get the value behind the given `key`. Returns `None` if the key doesn't exist.
    ///
    /// # Panics
    ///
    /// If `key` cannot be cast to `usize`.
    pub fn get(&self, key: K) -> Option<V> {
        let ukey = key.to_usize().unwrap();
        if ukey >= self.cap {
            return None;
        }

        let r = self.sparse[ukey];
        if r < self.dense.len() && self.dense[r].key == key {
            return Some(self.dense[r].value);
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
    pub fn update<F>(&mut self, key: K, f: F, default: V) -> bool
    where
        F: Fn(V) -> V,
    {
        let ukey = key.to_usize().unwrap();
        if ukey >= self.cap {
            self.insert(key, default);
            return false;
        }

        let r = self.sparse[ukey];
        if r < self.dense.len() && self.dense[r].key == key {
            self.dense[r].value = f(self.dense[r].value);
            true
        } else {
            self.insert(key, default);
            false
        }
    }

    /// Removes a key-value pair from the map. Returns whether the pair was present in the set.
    ///
    /// # Panics
    ///
    /// If `key` cannot be cast to `usize`.
    pub fn remove(&mut self, key: K) -> bool {
        let ukey = key.to_usize().unwrap();
        if ukey >= self.cap {
            return false;
        }

        let r = self.sparse[ukey];

        // Remove only if the pair is part of the map.
        if r < self.dense.len() && self.dense[r].key == key {
            // Remove the pair by giving its slot to the last pair in `dense`.
            let last_pair = self.dense[self.dense.len() - 1];
            self.sparse[last_pair.key.to_usize().unwrap()] = r; // Update `last_pair`'s link into `sparse`.
            self.dense[r] = last_pair;

            // Delete the now expendable copy of `last_pair`.
            self.dense.pop();

            return true;
        }

        false
    }

    /// Returns true if the set contains no elements.
    pub fn is_empty(&self) -> bool {
        self.dense.is_empty()
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.dense.len()
    }

    /// Removes all elements from the map.
    ///
    /// This operation is O(1). It does not deallocate memory.
    pub fn clear(&mut self) {
        // The dense array contains pairs of integers, so no destructors need to be called.
        self.dense.clear();
    }

    /// An iterator visiting all elements in arbitrary order.
    pub fn iter(&self) -> SparseMapIter<'_, K, V> {
        SparseMapIter {
            iter: self.dense.iter(),
        }
    }
}

/// An iterator over the key-value pairs of a [`SparseMap`].
///
/// This struct is created by the [`iter`] method on [`SparseMap`].
///
/// [`iter`]: SparseMap::iter
pub struct SparseMapIter<'a, K: PrimInt + Unsigned, V: Copy> {
    iter: std::slice::Iter<'a, Pair<K, V>>,
}

impl<'a, K: PrimInt + Unsigned, V: Copy> Iterator for SparseMapIter<'a, K, V> {
    type Item = &'a Pair<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

// `IntoIterator` implementation for [`SparseMap`].
impl<K: Unsigned + PrimInt, V: Copy> IntoIterator for SparseMap<K, V> {
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
pub struct SparseMapIntoIter<K: PrimInt + Unsigned, V: Copy> {
    iter: std::vec::IntoIter<Pair<K, V>>,
}

impl<K: PrimInt + Unsigned, V: Copy> Iterator for SparseMapIntoIter<K, V> {
    type Item = Pair<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

pub struct SparseSet<T: Unsigned + PrimInt> {
    inner: SparseMap<T, ()>,
}

impl<T: Unsigned + PrimInt> SparseSet<T> {
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
        self.inner.remove(value)
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
}

/// An iterator over the elements of a `SparseSet`.
///
/// This struct is created by the [`iter`] method on [`SparseSet`].
///
/// [`iter`]: SparseSet::iter
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

impl<T: Unsigned + PrimInt> IntoIterator for SparseSet<T> {
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
        assert_eq!(map.get(0), Some(1));
        assert_eq!(map.get(41), Some(2));
        assert_eq!(map.get(14), None);

        map.update(41, |n| n * n, 0);
        assert_eq!(map.get(41), Some(4));
        map.update(14, |n| n, 10);
        assert_eq!(map.get(14), Some(10));

        map.clear();

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
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
        assert!(m.remove(390));
        assert!(m.remove(200));
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
        assert!(!set.contains(5));
        assert!(set.contains(6));
        assert!(set.contains(7));

        set.clear();

        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
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

    fn gen_random_vec(size: usize) -> Vec<u32> {
        let mut rng = rand::thread_rng();
        let mut vec = Vec::with_capacity(size);

        for _ in 0..size {
            vec.push(rng.gen_range(0..10000));
        }

        vec
    }
}
