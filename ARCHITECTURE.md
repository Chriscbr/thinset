# Design

In many ways, `thinset` is a somewhat peculiar kind of map. This file gives an overview of the key ideas that underlie `thinset`.

## Commit to using memory for speed

`thinset` uses a big array (called `sparse`) whose length is at least equal to the value of the biggest key in the map. This is what makes `thinset` fast. Looking up a value means reading the value in this array at the position of the key (and then performing some tiny checks to find the key's actual value).

The cost of `thinset`'s high speed is increased memory usage. However, most computers have huge amounts of memory now, and even bigger virtual address spaces (256 terabytes on x86_64). Thus, `thinset` takes advantage of the memory abundance to achieve better performance.

## Be smart about using memory

The `thinset` library is based on an algorithm described by Briggs and Torczon in their 1993 paper "An efficient representation for sparse sets". Their key insight is a method of using large chunks of memory to store and retrieve data without needing to initialize any of that memory beforehand. There are multiple advantages to this method.

First off, initializing memory before use (e.g., by overwriting all data with 0s) takes an amount of time that can be proportional to the amount of memory used. To compare creating a Rust `Vec` of some size with and without initializing it, see [this benchmark](https://gist.github.com/Chriscbr/14880202eb941c7c7540995d95a96664).

In addition, virtual paging disconnects the memory that programs think they have from the physical memory that they really consume. Many operating systems don't allocate physical pages until they are touched.[^1] So, allocating large chucks of uninitialized memory might have a negligible effect if only small amounts of that allocation are used.

In practice, these effects combine to make `thinset` more memory efficient than it might seem at the surface.

# Implementation

> [!NOTE]
> This part might be subject to greater change depending on the library's state.

In general, `thinset` aims to adhere idiomatic Rust. Tiny amounts of `unsafe` code are used, but they are clearly documented, and easy to reason about.

## `SparseMap` and `SparseSet`

The core of `thinset` is implemented in the `SparseMap` structure. This structure is a typical key-value map from unsigned integer keys to arbitrary values. `SparseSet` is a set of unsigned integers. It is implemented in terms of `SparseMap` as a map from unsigned integer keys to `()` values. There is effectively no runtime cost of mapping to `()` since [its size is 0](https://github.com/Chriscbr/thinset/blob/6ec2eb4b6e2868bd89595822d4c040e50876daf4/src/lib.rs#L1254), and [key-value pairs are inserted together](https://github.com/Chriscbr/thinset/blob/6ec2eb4b6e2868bd89595822d4c040e50876daf4/src/lib.rs#L241p) such that there is no insertion code to be saved.

The Rust Standard Library's [`HashSet`](https://doc.rust-lang.org/std/collections/struct.HashSet.html) is related to its `HashMap` in the same way, and uses the same `()` trick. That's where we got it from.

[^1]: This fact can be used in arena allocators too. For example, see ["Arena size and growth" in this article](https://nullprogram.com/blog/2023/09/27/#arena-size-and-growth) by Chris Wellons.
