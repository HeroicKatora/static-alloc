//! Provides the Fill trait, an alternative to Extend for finite containers.
//!
//! # Motivation
//!
//! The `Extend` trait of the standard library and other interactions with iterators have some
//! deficiencies in resource constrained environments. For the most part, they assume either
//! infinite resources or that one might panic when memory is exhausted. To illustrate this problem
//! recall that there is no `Vec::push` can always reallocate and `(0..).collect::<Vec<_>>()` will
//! almost surely exit in a panic.
//!
//! The official recommendation for the `Extend` trait is to simulate pushing all items from the
//! iterator as if by executing the potentially panicking loop:
//!
//! ```
//! # let iter: Option<usize> = None;
//! # let mut collection = vec![];
//! for item in iter {
//!     collection.push(item);
//! }
//! ```
//!
//! However this can not react to having exhausted the available space within the collection. This
//! is where the `Fill` comes in. Instead of looping over all items the implementors should only
//! pull items from the iterator while space is available. The remaining items of the iterator can
//! then be handled with a fall-back path or ignored.
//!
//! # Example
//!
//! An option can be viewed as a collection with a capacity of one. One can fill it with the first
//! item of an iterator if it is empty.
//!
//! ```
//! use fill::Fill;
//! let mut memory = None;
//!
//! memory.fill(42..);
//! assert_eq!(memory, Some(42));
//! ```

#![no_std]
#![deny(missing_docs)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod assign;
mod fill;

pub use crate::assign::Assign;
pub use crate::fill::Fill;

pub trait IntoIteratorExt: IntoIterator {
    fn assign<'item, T: 'item>(self) -> Assign<Self::IntoIter>
    where
        Self: Sized + IntoIterator<Item=&'item mut T>,
        Self::IntoIter: ExactSizeIterator,
    {
        Assign::<Self::IntoIter>::new(self.into_iter())
    }
}

impl<T: IntoIterator> IntoIteratorExt for T { }

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
