use thinset::{SparseSet, set};

fn main() {
    let mut set: SparseSet<u32> = set![4, 32, 16, 24, 63];
    assert!(set.contains(32));
    assert!(set.contains(63));

    set.insert(25);

    println!("Set contents:");
    for x in set.iter() {
        println!("{x}");
    }
}