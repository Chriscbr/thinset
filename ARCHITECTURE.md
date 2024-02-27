# Design: Commit to using memory for speed

In many ways, `thinset` is a somewhat peculiar kind of map. This file gives an overview of the ideas that underlie `thinset`.

`thinset` uses a big array (called `sparse`) whose length is at least equal to the value of the biggest key in the map. This is what makes `thinset` fast. Looking up a value means reading the value in this array at the position of the key (and then performing some tiny checks to find the key's actual value).

The cost of `thinset`'s high speed is increased memory usage. However, most computers have huge amounts of memory now, and even bigger virtual address spaces (256 terabytes on x86_64). Thus, `thinset` takes advantage of the memory abundance to achieve better performance.

The `thinset` library is based on an algorithm described by Briggs and Torczon in their 1993 paper "An efficient representation for sparse sets". They present a method of using large chunks of memory to store and retrieve data without initializing any of that memory beforehand. For reasons related to Rust's memory model, it seems that this is [impossible to implement in Rust](https://www.ralfj.de/blog/2019/07/14/uninit.html) without introducing undefined behavior. So, while this method of using uninitialized memory might reduce the number of physical pages used and could speed up the process of creating sets with large universes, it is not part of this implementation.

# Implementation

> [!NOTE]
> This part might be subject to greater change depending on the library's state.

In general, `thinset` aims to adhere idiomatic Rust. There is no `unsafe` code used.

## `SparseMap` and `SparseSet`

The core of `thinset` is implemented in the `SparseMap` structure. This structure is a typical key-value map from unsigned integer keys to arbitrary values. `SparseSet` is a set of unsigned integers. It is implemented in terms of `SparseMap` as a map from unsigned integer keys to `()` values. There is effectively no runtime cost of mapping to `()` since [its size is 0](https://github.com/Chriscbr/thinset/blob/6ec2eb4b6e2868bd89595822d4c040e50876daf4/src/lib.rs#L1254), and [key-value pairs are inserted together](https://github.com/Chriscbr/thinset/blob/6ec2eb4b6e2868bd89595822d4c040e50876daf4/src/lib.rs#L241p) such that there is no insertion code to be saved.

The Rust Standard Library's [`HashSet`](https://doc.rust-lang.org/std/collections/struct.HashSet.html) is related to its `HashMap` in the same way, and uses the same `()` trick. That's where we got it from.
