# static-alloc

[![Crates.io Status](https://img.shields.io/crates/v/static-alloc.svg)](https://crates.io/crates/static-alloc)
[![Docs.rs Status](https://docs.rs/static-alloc/badge.svg)](https://docs.rs/static-alloc/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/HeroicKatora/static-alloc/LICENSE)
[![CI Status](https://api.cirrus-ci.com/github/HeroicKatora/static-alloc.svg)](https://cirrus-ci.com/github/HeroicKatora/static-alloc)

Replacements for `alloc` that do not perform any allocation themselves.

## Goal and Target Platform

Provides allocator based data structures for extremely resource constrained
environments where the only memory guaranteed is your program's image in memory
as provided by the loader. This includes `Box`, `Rc`, a `FixedVec`, and a `Slab`
allocator to create the structures.

This library aims to provide functionality similar to the standard `alloc`
crate. It is obviously far from complete, and contributions with bug fixes or
more allocators are welcome. As a general principle those should provide
mechanisms, not policy, have a usable direct api that does not require them to
override any singleton such as the single global allocator.

Possible use cases are OS-less development, embedded, bootloaders (even
stage0/1 maybe, totally untested). The primary goals are similar to the
standard library simplicity, and correctness, and minimal assumptions.

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

## Contributing

PRs introducing more tests or documentation are very welcome! Whatever else
submitted should have simplicity and composability in mind, ideas that can not
be put into a draft form are likely too complex or not focussed enough. PRs
should be *extremely* reluctant with introducing new dependencies and *should*
contain no non-optional dependency.

Please open issues with drafts only, feature requests and 'help' issues will be
closed (if you are lucky with a final comment). Stability trumps growth. I
simply can not make any longterm commitment outside my intrinsic motiviation
towards this project. Hence, I favour a highly usable core over a large
interface that is only somewhat usable.

## Additional

This project is mainly MIT licensed. You may alternatively choose [the
Unlicense](http://unlicense.org/) instead in which case the copyright headers
signify the parts dedicated to the public domain to the fullest possible extent
instead.
