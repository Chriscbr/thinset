//! An implementation of a set using a pair of sparse and dense arrays as backing stores.
//!
//! This type of set is useful when you need to efficiently track set membership for integers
//! from a large universe, but the values are relatively spread apart.
//!
//! The sparse set supports constant-time insertion, removal, lookups.
//!
//! Compared to the standard library's `HashSet`, clearing the set is constant-time instead of
//! linear time.
//! Compared to bitmap-based sets like the `bit-set` crate, iteration over the set is
//! proportional to the cardinality of the set (how many elements you have) instead of proportional
//! to the maximum size of the set.
//! The only downside is that the set requires more memory than other set implementations.
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

use num_traits::PrimInt;
use num_traits::Unsigned;

/// A sparse set of integer values.
pub struct SparseSet<T: PrimInt + Unsigned> {
    cap: usize,
    sparse: Vec<usize>,
    dense: Vec<T>,
}

impl<T: PrimInt + Unsigned> SparseSet<T> {
    /// Creates an empty SparseSet.
    pub fn new() -> Self {
        Self::with_capacity(0x1000)
    }

    /// Creates an empty SparseSet that's allocated to store elements
    /// with values up to `cap - 1` without allocating more memory.
    ///
    /// If `cap` is greater than the largest number of unique `T`s, then the capacity
    /// of the set is decreased to only hold exactly the largest number of unique `T`s.
    /// For example, if `T` is `u8` and the capacity `10000` is given, only `255`
    /// elements will be allocated, because it's impossible for a set of `u8`s to hold
    /// any more elements than `255`.
    #[allow(clippy::uninit_vec)]
    pub fn with_capacity(cap: usize) -> Self {
        // If the system's size allows it, `max_cap` is big enough to hold all unique `T`s.
        let max_cap = T::max_value()
            .to_usize()
            .unwrap_or(usize::MAX)
            .saturating_add(1);
        let cap = cap.min(max_cap);

        // Allocate a vector size `cap` and initialize it with garbage values.
        // SAFETY: The call to `with_capacity(cap)` ensures that `set_len(cap)`
        // will succeed. `sparse` maybe be filled with garbage simply based on how
        // the set works. An element is only considered part of the set if the entires
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

    /// Returns true if the set contains a value.
    ///
    /// # Panics
    ///
    /// If `value` cannot be cast to `usize`.
    pub fn contains(&self, value: T) -> bool {
        let uvalue = value.to_usize().unwrap();
        if uvalue >= self.cap {
            return false;
        }

        let r = self.sparse[uvalue];

        r < self.dense.len() && self.dense[r] == value
    }

    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    /// - If the set did not previously contain this value, true is returned.
    /// - If the set already contained this value, false is returned, and the set is not modified.
    /// 
    /// # Panics
    /// 
    /// If `value` cannot be cast to `usize`. 
    pub fn insert(&mut self, value: T) -> bool {
        let uvalue = value.to_usize().unwrap();
        if uvalue >= self.cap {
            self.grow_to_max(uvalue);
        }

        let r = self.sparse[uvalue];

        // If the value is already in the set, return early.
        if r < self.dense.len() && self.dense[r] == value {
            return false;
        }

        self.sparse[uvalue] = self.dense.len();
        self.dense.push(value);

        true
    }

    fn grow_to_max(&mut self, new_max: usize) {
        let cap = new_max
            .checked_add(1)
            .expect("maximum value is greater than the maximum allowed by the system's usize");
        // SAFETY: The call to `reserve_exact(cap - self.sparse.len())` ensures that the capacity is
        // greater or equal to `cap` so that `set_len(cap)` will succeed. See `Self::with_capacity`
        // for more info on uninitialized memory in `sparse`.
        self.sparse.reserve_exact(cap - self.sparse.len());
        unsafe {
            self.sparse.set_len(cap);
        }

        self.cap = cap;
    }

    /// Removes a value from the set. Returns whether the value was present in the set.
    ///
    /// # Panics
    ///
    /// If `value` cannot be cast to `usize`.
    pub fn remove(&mut self, value: T) -> bool {
        let uvalue = value.to_usize().unwrap();
        if uvalue >= self.cap {
            return false;
        }

        let r = self.sparse[uvalue];

        // If the value isn't in the set, return early.
        if r >= self.dense.len() || self.dense[r] != value {
            return false;
        }

        // Remove the value by giving its slot to the last value in `dense`.
        let last_value = self.dense[self.dense.len() - 1];
        self.dense[r] = last_value;
        self.sparse[last_value.to_usize().unwrap()] = r;  // Update `last_value`'s link into `sparse`.
        self.dense.pop();  // Delete the now expendable copy of `last_value` from the end of `dense`.

        true
    }
 
    /// Returns true if the set contains no elements.
    pub fn is_empty(&self) -> bool {
        self.dense.is_empty()
    }

    /// Returns the number of elements in the set.
    pub fn len(&self) -> usize {
        self.dense.len()
    }

    /// Removes all elements from the set.
    ///
    /// This operation is O(1). It does not deallocate memory.
    pub fn clear(&mut self) {
        // The dense array contains integers, so no destructors need to be called.
        self.dense.clear();
    }

    /// An iterator visiting all elements in arbitrary order.
    pub fn iter(&self) -> SparseSetIter<'_, T> {
        SparseSetIter {
            iter: self.dense.iter(),
        }
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

/// An iterator over the elements of a `SparseSet`.
///
/// This struct is created by the [`iter`] method on [`SparseSet`].
///
/// [`iter`]: SparseSet::iter
pub struct SparseSetIter<'a, T: PrimInt + Unsigned> {
    iter: std::slice::Iter<'a, T>,
}

impl<'a, T: PrimInt + Unsigned> Iterator for SparseSetIter<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().copied()
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
            iter: self.dense.into_iter(),
        }
    }
}

/// An iterator over the elements of a `SparseSet`.
///
/// This struct is created by the [`into_iter`] method on [`SparseSet`].
///
/// [`into_iter`]: SparseSet::into_iter
pub struct SparseSetIntoIter<T: PrimInt + Unsigned> {
    iter: std::vec::IntoIter<T>,
}

impl<T: PrimInt + Unsigned> Iterator for SparseSetIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
                    9,
                    10,
                    11,
                    100,  // Note the trailing comma is allowed for visual uniformity.
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
        let mut set: SparseSet<usize> = SparseSet::with_capacity(0);
        assert_eq!(set.len(), 0);
        assert!(!set.contains(0));
        assert!(!set.contains(100));
        set.insert(4);
        assert!(set.contains(4));
    }

    #[test]
    fn sparse_set_fit_bounds() {
        let mut s: SparseSet<u8> = SparseSet::with_capacity(u8::MAX as usize + 10);
        for i in 0..u8::MAX {
            s.insert(i);
        }
        for i in 0..u8::MAX {
            assert!(s.contains(i));
        }
        assert_eq!(s.len(), u8::MAX as usize);
        for i in 0..u8::MAX {
            assert!(s.remove(i));
        }
        assert_eq!(s.len(), 0);
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
    fn sparse_set_allows_random_insertions() {
        use rand::Rng;
        let mut rng = rand::thread_rng();

        let n_iters = rng.gen_range(0x100..0x1000);
        let mut check = Vec::with_capacity(n_iters);

        let mut s: SparseSet<u32> = SparseSet::new();
    
        // Check that inserting random values works.
        for _ in 0..n_iters {
            let x = rng.gen_range(0..10000);
            s.insert(x);
            check.push(x);
        }
        
        // Check that all of the inserted values are actually inserted.
        for &x in &check {
            assert!(s.contains(x));
        }

        // After removing every element at least once, the set should be empty.
        // `check` can contain duplicates, so the same value might be removed
        // more than once.
        for &x in &check {
            s.remove(x);
        }
        assert!(s.is_empty());
    }
}
