# without-alloc

[![Crates.io Status](https://img.shields.io/crates/v/without-alloc.svg)](https://crates.io/crates/without-alloc)
[![Docs.rs Status](https://docs.rs/without-alloc/badge.svg)](https://docs.rs/without-alloc/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/HeroicKatora/without-alloc/LICENSE)
[![CI Status](https://api.cirrus-ci.com/github/HeroicKatora/alloc-free.svg)](https://cirrus-ci.com/github/HeroicKatora/alloc-free)

Dynamic data structures that do not require a global allocator.

## Usage

This allows creating dynamic and recursive data structures without dynamic
allocations. The example below makes use of the `static-alloc` crate to build a
list with static lifetime based on dynamic data. As local memory pools for
fixed capacity `FixedVec`:

```rust
use static_alloc::Bump;
use without_alloc::{FixedVec, alloc::LocalAllocLeakExt};

let mut pool: Bump<[usize; 16]> = Bump::uninit();
// Allocate a vector with capacity of 16 from the slab.
let mut vector = pool.fixed_vec(16).unwrap();

let mut num = 0;
// Push mutable ref, not `'static`, `Copy` nor `Clone`!
vector.push(&mut num);
*vector[0] = 42;

drop(vector);
assert_eq!(num, 42);
```

This might be handy if you want to chain boot another kernel and pass it a
linked list describing the platform.

```rust
use static_alloc::Bump;
use without_alloc::{Box, alloc::LocalAllocLeakExt};

enum List {
    Nil,
    Cons(u8, Box<'static, List>),
}

static SLAB: Bump<[u8; 1024]> = Bump::uninit();

let base = SLAB.boxed(List::Nil).unwrap();
let one = SLAB.boxed(List::Cons(0, base)).unwrap();
let two = SLAB.boxed(List::Cons(1, one)).unwrap();
```

