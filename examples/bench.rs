#[macro_use]
extern crate bencher;

use bencher::{black_box, Bencher};
use rand::{thread_rng, RngCore};
use thinset::SparseSet;

const BITS: usize = 2 << 16;

fn bench_sparse_set(b: &mut Bencher) {
    let mut r = thread_rng();
    let mut set = SparseSet::with_capacity(BITS);
    b.iter(|| {
        for _ in 0..1000 {
            set.insert((r.next_u32() as usize) % BITS);
        }
        for x in set.iter() {
            black_box(x);
        }
        set.clear();
    });
}

fn bench_hash_set(b: &mut Bencher) {
    let mut r = thread_rng();
    let mut set = std::collections::HashSet::new();
    b.iter(|| {
        for _ in 0..1000 {
            set.insert((r.next_u32() as usize) % BITS);
        }
        for x in set.iter() {
            black_box(x);
        }
        set.clear();
    });
}

fn bench_bit_set(b: &mut Bencher) {
    let mut r = thread_rng();
    let mut set = bit_set::BitSet::new();
    b.iter(|| {
        for _ in 0..1000 {
            set.insert((r.next_u32() as usize) % BITS);
        }
        for x in set.iter() {
            black_box(x);
        }
        set.clear();
    });
}

benchmark_group!(benches, bench_sparse_set, bench_hash_set, bench_bit_set);
benchmark_main!(benches);
