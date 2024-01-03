use std::env;
use thinset::{Pair, SparseMap};

fn main() {
    let mut args = env::args();
    args.next();
    let s = args
        .next()
        .expect("Pass a string to count the number of characters of");

    let mut map = SparseMap::new();
    for ch in s.chars() {
        map.update(ch as u8, 1, |n| n + 1);
    }

    println!("The following characters occur in the string '{}':", s);
    for Pair { key, value } in map.iter() {
        if *value == 1 {
            println!(" '{}' once", *key as char);
        } else {
            println!(" '{}' {} times", *key as char, *value);
        }
    }
}
