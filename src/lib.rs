use std::{
    cell::{Ref, RefCell},
    ops::Deref,
};

/// An array with O(1) random access operations that doesn't require
/// memory to be initialized with zero values.
/// Accessing an index that has not been set before will return 0.
///
/// In practice, this isn't that worthwhile since `vec![0; length]` is pretty efficient;
/// the OS usually has some zeroed memory on hand.
pub struct SparseUsizeArray {
    sparse: RefCell<Vec<usize>>, // raw array
    dense: RefCell<Vec<usize>>,
    data: RefCell<Vec<usize>>, // raw array
    size: usize,
}

impl SparseUsizeArray {
    pub fn new(size: usize) -> Self {
        let mut sparse: Vec<usize> = Vec::with_capacity(size);
        let dense: Vec<usize> = Vec::new();
        let mut data: Vec<usize> = Vec::with_capacity(size);

        // fill the sparse and data vectors without initializing them
        unsafe {
            sparse.set_len(size);
            data.set_len(size);
        }

        Self {
            sparse: RefCell::new(sparse),
            dense: RefCell::new(dense),
            data: RefCell::new(data),
            size,
        }
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn at(&self, index: usize) -> usize {
        if index >= self.size {
            panic!("index out of bounds");
        }

        let mut sparse = self.sparse.borrow_mut();
        let mut dense = self.dense.borrow_mut();
        let mut data = self.data.borrow_mut();

        // sparse[index] will give us some number back -- either trash, or a valid position into the `dense` array
        let r: usize = unsafe { *sparse.get_unchecked(index) };

        // if the number isn't beyond the size of `dense` and the corresponding position in `dense` matches the index we were searching for,
        // it means we already set a value for this index, so it can be read from the `data` array
        if r < dense.len() && dense[r] == index {
            return data[index];
        }

        // otherwise, we add a new entry to `dense` and store the index of that entry inside `sparse`
        sparse[index] = dense.len();
        dense.push(index);
        data[index] = 0;
        0
    }

    pub fn set(&mut self, index: usize, value: usize) {
        if index >= self.size {
            panic!("index out of bounds");
        }

        let mut sparse = self.sparse.borrow_mut();
        let mut dense = self.dense.borrow_mut();
        let mut data = self.data.borrow_mut();

        // sparse[index] will give us some number back -- either trash, or a valid position into the `dense` array
        let r: usize = unsafe { *sparse.get_unchecked(index) };

        // if the number isn't beyond the size of `dense` and the corresponding position in `dense` matches the index we were searching for,
        // it means we already set a value for this index, so we can update the `data`` array directly
        if r < dense.len() && dense[r] == index {
            data[index] = value;
            return;
        }

        // otherwise, we add a new entry to `dense` and store the index of that entry inside `sparse`
        sparse[index] = dense.len();
        dense.push(index);
        data[index] = value;
    }
}

/// An array with O(1) random access operations that doesn't require
/// memory to be initialized with zero values.
/// Accessing an index that has not been set before will return T::default().
pub struct SparseArray<T: Default> {
    sparse: RefCell<Vec<usize>>, // raw array
    dense: RefCell<Vec<usize>>,
    data: RefCell<Vec<T>>, // raw array
    size: usize,
}

impl<T: Default> SparseArray<T> {
    pub fn new(size: usize) -> Self {
        let mut sparse: Vec<usize> = Vec::with_capacity(size);
        let dense: Vec<usize> = Vec::new();
        let mut data: Vec<T> = Vec::with_capacity(size);

        // fill the sparse and data vectors without initializing them
        unsafe {
            sparse.set_len(size);
            data.set_len(size);
        }

        Self {
            sparse: RefCell::new(sparse),
            dense: RefCell::new(dense),
            data: RefCell::new(data),
            size,
        }
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    // TODO: it might be possible to provide a cleaner API using UnsafeCell
    pub fn at(&self, index: usize) -> impl Deref<Target = T> + '_ {
        if index >= self.size {
            panic!("index out of bounds");
        }

        let mut sparse = self.sparse.borrow_mut();
        let mut dense = self.dense.borrow_mut();
        // let mut data = self.data.borrow_mut();

        // sparse[index] will give us some number back -- either trash, or a valid position into the `dense` array
        let r: usize = unsafe { *sparse.get_unchecked(index) };

        // if the number isn't beyond the size of `dense` and the corresponding position in `dense` matches the index we were searching for,
        // it means we already set a value for this index, so it can be read from the `data` array
        if r < dense.len() && dense[r] == index {
            return Ref::map(self.data.borrow(), |data| &data[index]);
        }

        // otherwise, we add a new entry to `dense` and store the index of that entry inside `sparse`
        sparse[index] = dense.len();
        dense.push(index);

        let mut data = self.data.borrow_mut();
        data[index] = T::default();
        std::mem::drop(data);

        Ref::map(self.data.borrow(), |data| &data[index])
    }

    pub fn set(&mut self, index: usize, value: T) {
        if index >= self.size {
            panic!("index out of bounds");
        }

        let mut sparse = self.sparse.borrow_mut();
        let mut dense = self.dense.borrow_mut();
        let mut data = self.data.borrow_mut();

        // sparse[index] will give us some number back -- either trash, or a valid position into the `dense` array
        let r: usize = unsafe { *sparse.get_unchecked(index) };

        // if the number isn't beyond the size of `dense` and the corresponding position in `dense` matches the index we were searching for,
        // it means we already set a value for this index, so we can update the `data`` array directly
        if r < dense.len() && dense[r] == index {
            data[index] = value;
            return;
        }

        // otherwise, we add a new entry to `dense` and store the index of that entry inside `sparse`
        sparse[index] = dense.len();
        dense.push(index);
        data[index] = value;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sparse_usize_array_get() {
        let arr = SparseUsizeArray::new(5);
        assert_eq!(arr.len(), 5);

        assert_eq!(arr.at(2), 0);
        assert_eq!(arr.at(2), 0);
        assert_eq!(arr.at(3), 0);
    }

    #[test]
    fn sparse_usize_array_set() {
        let mut arr = SparseUsizeArray::new(5);
        assert_eq!(arr.len(), 5);

        assert_eq!(arr.at(2), 0);
        arr.set(2, 42);
        assert_eq!(arr.at(2), 42);

        arr.set(3, 1234);
        assert_eq!(arr.at(3), 1234);
    }

    #[should_panic]
    #[test]
    fn sparse_usize_array_index_out_of_bounds() {
        let arr = SparseUsizeArray::new(0);
        assert_eq!(arr.len(), 0);
        arr.at(0);
    }

    #[test]
    fn sparse_array_get() {
        let arr: SparseArray<String> = SparseArray::new(5);
        assert_eq!(arr.len(), 5);

        assert_eq!(*arr.at(2), String::default());
        assert_eq!(*arr.at(2), String::default());
        assert_eq!(*arr.at(3), String::default());
    }

    #[test]
    fn sparse_array_set() {
        let mut arr = SparseArray::new(5);
        assert_eq!(arr.len(), 5);

        assert_eq!(*arr.at(2), String::default());
        arr.set(2, "hello".to_string());
        assert_eq!(*arr.at(2), "hello".to_string());

        arr.set(3, "world".to_string());
        assert_eq!(*arr.at(3), "world".to_string());
    }

    #[should_panic]
    #[test]
    fn sparse_array_index_out_of_bounds() {
        let arr: SparseArray<String> = SparseArray::new(0);
        assert_eq!(arr.len(), 0);
        arr.at(0);
    }
}
