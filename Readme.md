# static-alloc

Replacements for `alloc` without dynamic allocation.

## Goal and Target Platform

Provides allocator based data structures for extremely resource constrained
environments where the only memory guaranteed is your program's image in memory
as provided by the loader. This includes a `Slab`-allocator and a `FixedVec`.

Possible use cases are OS-less development, embedded, bootloaders (even
stage0/1 maybe, totally untested). The primary goals are minimalism,
simplicity, and correctness.

This library aims to provide functionality similar to the standard `alloc`
crate. It is obviously far from complete, and contributions with bug fixes or
more allocators are welcome. As a general principle those should provide
mechanisms, not policy, have a usable direct api that does not require them to
override any singleton such as the single global allocator.

Feature requests and 'help' issues will be closed, drafts will be decided on
the spot. Whatever submitted should have simplicity and composability in mind,
ideas that can not be put into a draft form are likely too complex or not
focussed enough. PRs should be *extremely* reluctant with introducing new
dependencies and *should* contain no non-optional dependency.

## Usage

As a global allocator for `alloc`:

```rust
use static_alloc::Slab;

#[global_allocator]
static A: Slab<[u8; 1 << 16]> = Slab::uninit();

fn main() {
    // Vec occupying `1 << 7` bytes
    let v = vec![0xdeadbeef_u32; 32];

    // … or allocate values directly.
    let buffer: &mut [u32; 32] = A.leak([0; 32])
        .unwrap();
    buffer.copy_from_slice(&v);
}
```

For recursive data structures:

```rust
use static_alloc::{Box, Slab};

enum List {
    Nil,
    Cons(u8, Box<'static, List>),
}

static SLAB: Slab<[u8; 1024]> = Slab::uninit();

let base = SLAB.boxed(List::Nil).unwrap();
let one = SLAB.boxed(List::Cons(0, base)).unwrap();
let two = SLAB.boxed(List::Cons(1, one)).unwrap();
```

As local memory pools for fixed capacity `FixedVec`:

```rust
use static_alloc::{FixedVec, Uninit};
use core::mem::MaybeUninit;

let mut pool = MaybeUninit::<[u8; 1024]>::uninit();
let memory = Uninit::from(&mut pool);
let mut vector = FixedVec::from_available(memory);

let mut num = 0;
// Push mutable ref, not `'static`, `Copy` nor `Clone`!
vector.push(&mut num);
*vector[0] = 42;

drop(vector);
assert_eq!(num, 42);
```

## Additional
[![Crates.io Status](https://img.shields.io/crates/v/static-alloc.svg)](https://crates.io/crates/static-alloc)
[![Docs.rs Status](https://docs.rs/static-alloc/badge.svg)](https://docs.rs/static-alloc/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/HeroicKatora/static-alloc/LICENSE)
[![CI Status](https://api.cirrus-ci.com/github/HeroicKatora/static-alloc.svg)](https://cirrus-ci.com/github/HeroicKatora/static-alloc)

This project is mainly MIT licensed. You may alternatively choose [the
Unlicense](http://unlicense.org/) instead in which case the copyright headers
signify the parts dedicated to the public domain to the fullest possible extent
instead.
