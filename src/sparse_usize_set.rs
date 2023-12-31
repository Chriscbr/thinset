/// A sparse set of usize values, that supports
/// constant-time insertion, removal, lookup, and clearing,
/// as well as iteration that is proportional to the cardinality of the set
/// rather than the maximum size of the set.
///
/// The implementation isn't efficient in terms of space since it allocates
/// a vector of size `max_size` to store a sparse lookup table.
pub struct SparseUsizeSet {
    max_size: usize,
    sparse: Vec<usize>,
    dense: Vec<usize>,
}

impl SparseUsizeSet {
    #[allow(clippy::uninit_vec)] // TODO: remove
    pub fn new(max_size: usize) -> Self {
        // allocate a vector of size `max_size` and initialize it with garbage values
        let mut sparse = Vec::with_capacity(max_size);
        unsafe {
            sparse.set_len(max_size);
        }

        Self {
            max_size,
            sparse,            // sparse lookup table from index to position in dense
            dense: Vec::new(), // list of the values in the set
        }
    }

    pub fn contains(&self, value: usize) -> bool {
        if value >= self.max_size {
            panic!("value is greater than max_size");
        }

        let r = self.sparse[value];

        r < self.dense.len() && self.dense[r] == value
    }

    pub fn insert(&mut self, value: usize) {
        if value >= self.max_size {
            panic!("index out of bounds");
        }

        let r = self.sparse[value];

        // if the value is already in the set, return early
        if r < self.dense.len() && self.dense[r] == value {
            return;
        }

        self.sparse[value] = self.dense.len();
        self.dense.push(value);
    }

    // pub fn remove(&mut self, index: usize) {
    //     if index >= self.size {
    //         panic!("index out of bounds");
    //     }

    //     let r = self.sparse[index];

    //     if r < self.dense.len() && self.dense[r] == index {
    //         let last = self.dense.pop().unwrap();

    //         if last != index {
    //             self.dense[r] = last;
    //             self.sparse[last] = r;
    //         }
    //     }
    // }

    pub fn is_empty(&self) -> bool {
        self.dense.is_empty()
    }

    pub fn len(&self) -> usize {
        self.dense.len()
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
        assert!(!set.contains(5))
    }
}
