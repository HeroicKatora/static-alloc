//! General purpose global allocator(s) with static, inline storage.
//!
//! Provides an allocator for extremely resource constrained environments where the only memory
//! guaranteed is your program's image in memory as provided by the loader. Possible use cases are
//! OS-less development, embedded, bootloaders (even stage0/1 maybe, totally untested).
//!
//! ## Usage
//!
//! ```rust
//! use static_alloc::Slab;
//!
//! #[global_allocator]
//! static A: Slab<[u8; 1 << 16]> = Slab::uninit();
//!
//! fn main() {
//!     let v = vec![0xdeadbeef_u32; 128];
//!     println!("{:x?}", v);
//!
//!     let buffer: &'static mut [u32; 128] = A.leak([0; 128])
//!         .unwrap_or_else(|_| panic!("Runtime allocated before main"));
//! }
//! ```
//!
//! ## Why the name?
//!
//! This crates makes it safe to define a *static* object and to then use its memory to *allocate*
//! dynamic values without accidentally exposing or using uninitialized memory. This allows
//! obtaining `&'static mut T` instances which is handy if a struct requires a mutable reference
//! but it is also required that this struct has `'static` lifetime bounds itself.

// Copyright 2019 Andreas Molzer
#![no_std]
#![deny(missing_docs)]

pub mod bump;
pub use bump::Slab;

// Can't use the macro-call itself within the `doc` attribute. So force it to eval it as part of
// the macro invocation.
// 
// The inspiration for the macro and implementation is from
// <https://github.com/GuillaumeGomez/doc-comment>
//
// MIT License
//
// Copyright (c) 2018 Guillaume Gomez
macro_rules! insert_as_doc {
    { $content:expr } => {
        #[doc = $content] extern { }
    }
}

// Provides the README.md as doc, to ensure the example works!
insert_as_doc!(include_str!("../Readme.md"));
