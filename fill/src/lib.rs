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

/// Fill a collection from an iterator until its capacity has been reached.
///
/// # Examples
///
/// An option's capacity has been reached when it contains an item in a `Some`. It consumes no
/// items from the iterator when it already contains one and consumes exactly one if it is
/// currently `None`.
///
/// ```
/// # use fill::Fill;
/// let mut option = None;
///
/// let spilled = option.fill_and_keep_tail(42..);
/// assert_eq!(option, Some(42));
/// assert_eq!(spilled.start, 43);
/// ```
pub trait Fill<T> {
    /// Fill empty space with contents from an iterator.
    ///
    /// The iterator should be dropped and not exhausted when no more items can be pushed into the
    /// container.
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=T>;

    /// Fill the container from an iterator, returning it afterwards.
    ///
    /// This is only a shorthand for iterating by reference when the caller wants to inspect the
    /// state after filling or when a fall-back is supposed to consume remaining elements.
    fn fill_and_keep_tail<I>(&mut self, iter: I) -> I::IntoIter
        where I: IntoIterator<Item=T>
    {
        let mut iter = iter.into_iter();
        self.fill(&mut iter);
        iter
    }
}

#[cfg(feature = "alloc")]
/// Fills the vector as far as possible without reallocating.
impl<T> Fill<T> for alloc::vec::Vec<T> {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=T>
    {
        for item in iter.into_iter().take(self.capacity() - self.len()) {
            self.push(item);
        }
    }
}

#[cfg(feature = "alloc")]
/// Fills the queue as far as possible without reallocating.
impl<T> Fill<T> for alloc::collections::VecDeque<T> {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=T>
    {
        for item in iter.into_iter().take(self.capacity() - self.len()) {
            self.push_back(item);
        }
    }
}

/// Consumes all items until the first `None`.
impl Fill<()> for () {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=()>
    {
        for () in iter { }
    }
}

/// If the option does not yet contain an item, insert the next item of the iterator.
///
/// Note that this will call `iter.next()` at most once. The option will still be empty if the
/// iterator is not fused and returns `None` as the first result of that call.
impl<T> Fill<T> for Option<T> {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=T>
    {
        let mut iter = iter.into_iter();
        match self {
            None => *self = iter.next(),
            Some(_) => (),
        }
    }
}

/// Tries to fill the container in the `Ok`.
///
/// A result is full if it contains an error, or if the container in `Ok` is full.
impl<C, E, T> Fill<Result<T, E>> for Result<C, E>
    where C: Fill<T>,
{
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=Result<T, E>>
    {
        let mut iter = iter.into_iter();

        let container = match self {
            Ok(container) => container,
            Err(_) => return,
        };

        let err = loop {
            match iter.next() {
                None => return,
                Some(Err(err)) => break err,
                Some(Ok(ok)) => {
                    container.fill(core::iter::once(ok));
                },
            };
        };

        *self = Err(err);
    }
}

/// Advances self while inserting elements from the iterator.
impl<T> Fill<T> for core::slice::IterMut<'_, T> {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=T>
    {
        let mut iter = iter.into_iter();
        // Do not use `zip` to control the exact calls to `next`.
        while self.len() != 0 {
            if let Some(item) = iter.next() {
                *self.next().unwrap() = item;
            } else {
                break
            }
        }
    }
}

/// Advances self while swapping elements with the iterator.
impl<'a, T: 'a> Fill<&'a mut T> for core::slice::IterMut<'_, T> {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=&'a mut T>
    {
        let mut iter = iter.into_iter();
        // Do not use `zip` to control the exact calls to `next`.
        while self.len() != 0 {
            if let Some(item) = iter.next() {
                core::mem::swap(self.next().unwrap(), item);
            } else {
                break
            }
        }
    }
}

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
