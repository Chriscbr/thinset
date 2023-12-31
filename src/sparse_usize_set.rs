/// A sparse set of usize values, that supports
/// constant-time insertion, removal, lookup, and clearing,
/// as well as iteration that is proportional to the cardinality of the set
/// rather than the maximum size of the set.
///
/// The implementation isn't space efficient since it allocates
/// a vector of size `max_size` to store a sparse lookup table.
pub struct SparseUsizeSet {
    max_value: usize,
    sparse: Vec<usize>,
    dense: Vec<usize>,
}

impl SparseUsizeSet {
    /// Creates an empty SparseUsizeSet.
    ///
    /// The size of the universe of values must be specified. For example, if the set will contain
    /// values in the range [0, 1000), then `max_value` should be 1000.
    #[allow(clippy::uninit_vec)]
    pub fn new(max_value: usize) -> Self {
        // allocate a vector of size `max_value` and initialize it with garbage values
        let mut sparse = Vec::with_capacity(max_value);
        unsafe {
            sparse.set_len(max_value);
        }

        Self {
            max_value,
            sparse,            // sparse lookup table from index to position in dense
            dense: Vec::new(), // list of the values in the set
        }
    }

    /// Returns true if the set contains a value.
    pub fn contains(&self, value: usize) -> bool {
        if value >= self.max_value {
            panic!("value is greater than the set's max_value");
        }

        let r = self.sparse[value];

        r < self.dense.len() && self.dense[r] == value
    }

    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    /// - If the set did not previously contain this value, true is returned.
    /// - If the set already contained this value, false is returned, and the set is not modified.
    pub fn insert(&mut self, value: usize) -> bool {
        if value >= self.max_value {
            panic!("value is greater than the set's max_value");
        }

        let r = self.sparse[value];

        // if the value is already in the set, return early
        if r < self.dense.len() && self.dense[r] == value {
            return false;
        }

        self.sparse[value] = self.dense.len();
        self.dense.push(value);

        true
    }

    /// Removes a value from the set. Returns whether the value was present in the set.
    pub fn remove(&mut self, value: usize) -> bool {
        if value >= self.max_value {
            panic!("value is greater than the set's max_value");
        }

        let r = self.sparse[value]; // 0

        // if the value isn't in the set, return early
        if r >= self.dense.len() || self.dense[r] != value {
            return false;
        }

        // swap the value with the last value in the dense array
        let last_value = self.dense[self.dense.len() - 1];
        self.dense[r] = last_value;
        self.sparse[last_value] = r;

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
    pub fn iter(&self) -> SparseUsizeSetIter<'_> {
        SparseUsizeSetIter {
            iter: self.dense.iter(),
        }
    }
}

/// An iterator over the elements of a `SparseUsizeSet`.
///
/// This struct is created by the [`iter`] method on [`SparseUsizeSet`].
pub struct SparseUsizeSetIter<'a> {
    iter: std::slice::Iter<'a, usize>,
}

impl<'a> Iterator for SparseUsizeSetIter<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().copied()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl IntoIterator for SparseUsizeSet {
    type Item = usize;
    type IntoIter = SparseUsizeSetIntoIter;

    fn into_iter(self) -> Self::IntoIter {
        SparseUsizeSetIntoIter {
            iter: self.dense.into_iter(),
        }
    }
}

/// An iterator over the elements of a `SparseUsizeSet`.
///
/// This struct is created by the [`into_iter`] method on [`SparseUsizeSet`].
pub struct SparseUsizeSetIntoIter {
    iter: std::vec::IntoIter<usize>,
}

impl Iterator for SparseUsizeSetIntoIter {
    type Item = usize;

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
    fn sparse_usize_set() {
        let set = SparseUsizeSet::new(50);
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
    fn sparse_usize_set_iter() {
        let mut set = SparseUsizeSet::new(50);
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

    #[should_panic]
    #[test]
    fn sparse_usize_set_index_out_of_bounds() {
        let set = SparseUsizeSet::new(0);
        assert_eq!(set.len(), 0);
        set.contains(0);
    }
}
