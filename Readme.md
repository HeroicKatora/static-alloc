# static-alloc

General purpose global allocator(s) with static storage.

## Goal and Target Platform

Provides an allocator for extremely resource constrained environments where the
only memory guaranteed is your program's image in memory as provided by the
loader. Possible use cases are OS-less development, embedded, bootloaders (even
stage0/1 maybe, totally untested). The primary goals are minimalism,
simplicity, and correctness.

This library is far from complete, and contributions with bug fixes or more
allocators are welcome. As a general principle those should provide mechanisms,
not policy, have a usable direct api that does not require them to be
registered as the single global allocator.

Feature requests and 'help' issues will be closed, drafts will be decided on
the spot. With simplicity in mind, ideas that can not be put into a draft form
are likely too complex anyways. PRs should be extremely reluctant with
introducing new dependencies and *should* contain no non-optional dependency.

## Usage

```rust
use static_alloc::Slab;

#[global_allocator]
static A: Slab<[u8; 1 << 16]> = Slab::uninit();

fn main() {
    let v = vec![0xdeadbeef_u32; 128];
    println!("{:x?}", v);
}
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
