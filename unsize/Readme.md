# unsize

[![Crates.io Status](https://img.shields.io/crates/v/unsize.svg)](https://crates.io/crates/static-alloc)
[![Docs.rs Status](https://docs.rs/unsize/badge.svg)](https://docs.rs/unsize/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/HeroicKatora/static-alloc/LICENSE)
[![CI Status](https://api.cirrus-ci.com/github/HeroicKatora/static-alloc.svg)](https://cirrus-ci.com/github/HeroicKatora/static-alloc)

## Goals and Targets

This crate should work with `no_std` environments, for example to enable custom
`Box` designs that avoid any dependency on a global allocator, or an arena
based reference counted pointer, etc. For these use cases it is intended to
replace the nightly-only internal unsizing mechanism that the standard smart
pointers provide i.e. enable conversions such as `Box<[T; N]>` to `Box<[T]>`.

## Usage

As a library developer you can implement the `CoerciblePtr` trait for your
smart pointer type. This enables the use of all coercions with this pointer
type. To provide custom unsize coercions to your own `?Sized` wrapper type you
can provide a safe constructor for `Coercion`.

As a user of a `unsize`-enabled pointer type, you should import the
`CoerceUnsize` extension trait and the `Coercion` marker type. Then create an
instance of `Coercion` to 'coerce' the pointee type of a smart pointer.

## Additional

This project is licensed under Zlib OR Apache-2.0 OR MIT. You may alternatively
choose the Unlicense instead in which case the copyright headers signify the
parts dedicated to the public domain to the fullest possible extent instead.
