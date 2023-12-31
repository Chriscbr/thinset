//! An implementation of a set using a sparse and dense array as an underlying
//! representation for holding unsigned numbers.
//!
//! This type of set is useful when you need to efficiently track set membership for items
//! from a large universe, but the number of items in the sets is comparatively smaller.
//!
//! The sparse set supports constant-time insertion, removal, lookups.
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
//! // Specify a maximum value for the set
//! let mut s: SparseSet<usize> = SparseSet::new(100);
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
    max_value: T,
    sparse: Vec<usize>,
    dense: Vec<T>,
}

impl<T: PrimInt + Unsigned> SparseSet<T> {
    /// Creates an empty SparseSet.
    ///
    /// The size of the universe of values must be specified. For example, if the set will contain
    /// values in the range [0, 1000), then `max_value` should be 1000.
    #[allow(clippy::uninit_vec)]
    pub fn new(max_value: usize) -> Self {
        let max_value_capped = T::from(max_value)
            .expect("max_value is greater than the maximum value for the sparse set's type");

        // allocate a vector of size `max_value` and initialize it with garbage values
        let mut sparse = Vec::with_capacity(max_value);
        unsafe {
            sparse.set_len(max_value);
        }

        Self {
            max_value: max_value_capped,
            sparse,            // sparse lookup table from index to position in dense
            dense: Vec::new(), // list of the values in the set
        }
    }

    /// Returns true if the set contains a value.
    pub fn contains(&self, value: T) -> bool {
        if value >= self.max_value {
            panic!("value is greater than or equal to the set's max_value");
        }

        let uvalue = value.to_usize().unwrap();
        let r = self.sparse[uvalue];

        r < self.dense.len() && self.dense[r] == value
    }

    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    /// - If the set did not previously contain this value, true is returned.
    /// - If the set already contained this value, false is returned, and the set is not modified.
    pub fn insert(&mut self, value: T) -> bool {
        if value >= self.max_value {
            panic!("value is greater than or equal to the set's max_value");
        }

        let uvalue = value.to_usize().unwrap();
        let r = self.sparse[uvalue];

        // if the value is already in the set, return early
        if r < self.dense.len() && self.dense[r] == value {
            return false;
        }

        self.sparse[uvalue] = self.dense.len();
        self.dense.push(value);

        true
    }

    /// Removes a value from the set. Returns whether the value was present in the set.
    pub fn remove(&mut self, value: T) -> bool {
        if value >= self.max_value {
            panic!("value is greater than or equal to the set's max_value");
        }

        let uvalue = value.to_usize().unwrap();
        let r = self.sparse[uvalue]; // 0

        // if the value isn't in the set, return early
        if r >= self.dense.len() || self.dense[r] != value {
            return false;
        }

        // swap the value with the last value in the dense array
        let last_value = self.dense[self.dense.len() - 1];
        self.dense[r] = last_value;
        self.sparse[last_value.to_usize().unwrap()] = r;

        // remove the value from the dense array
        self.dense.pop();

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
        // the dense array contains integers, so no destructors need to be called
        self.dense.clear();
    }

    /// An iterator visiting all elements in arbitrary order.
    pub fn iter(&self) -> SparseSetIter<'_, T> {
        SparseSetIter {
            iter: self.dense.iter(),
        }
    }
}

/// An iterator over the elements of a `SparseSet`.
///
/// This struct is created by the [`iter`] method on [`SparseSet`].
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
        let set: SparseSet<usize> = SparseSet::new(50);
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
    fn sparse_set_iter() {
        let mut set: SparseSet<usize> = SparseSet::new(50);
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
        let mut set: SparseSet<usize> = SparseSet::new(50);
        set.insert(3);
        set.insert(4);
        set.insert(5);

        let mut iter = set.into_iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), None);
    }

    #[should_panic]
    #[test]
    fn sparse_set_contains_value_out_of_bounds() {
        let set: SparseSet<usize> = SparseSet::new(0);
        assert_eq!(set.len(), 0);
        set.contains(0);
    }

    #[should_panic]
    #[test]
    fn sparse_set_constructor_value_out_of_bounds() {
        let _set: SparseSet<u8> = SparseSet::new(u8::MAX as usize + 1);
    }
}
