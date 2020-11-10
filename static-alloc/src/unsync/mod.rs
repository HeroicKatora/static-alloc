//! This module defines a simple bump allocator.
//! The allocator is not thread safe.

mod bump;

use core::{cell::Cell, mem::ManuallyDrop, ptr::NonNull};

use bump::{Bump, BumpError, RawAllocError};
use crate::leaked::LeakBox;

/// An error representing an error while construction
/// a [`Chain`].
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct TryNewError {
    inner: RawAllocError,
}

impl TryNewError {
    /// Returns the allocation size of a `Chain`
    /// that couldn't be allocated.
    pub const fn allocation_size(&self) -> usize {
        self.inner.allocation_size()
    }
}

/// A `Chain` is a simple bump allocator, that draws
/// it's memory from another allocator. Chain allocators
/// can be chained together using [`Chain::chain`].
pub struct Chain {
    bump: Cell<NonNull<Bump>>,
}

impl Chain {
    /// Creates a new `Chain` that has a capacity of `size`
    /// bytes.
    pub fn new(size: usize) -> Result<Self, TryNewError> {
        Bump::alloc(size)
            .map(|bump| Self {
                bump: Cell::new(bump),
            }).map_err(|e| TryNewError { inner: e })
    }

    /// Attempts to allocate `elem` within the allocator.
    pub fn try_alloc<'bump, T>(&'bump self, elem: T) -> Result<LeakBox<'bump, T>, BumpError<T>> {
        unsafe {
            let bump_ptr = self.bump.as_ptr();
            (&*bump_ptr).as_ref().push(elem)
        }
    }

    /// Chains `self` together with `new`.
    pub fn chain(&self, new: Chain) {
        let new: ManuallyDrop<_> = ManuallyDrop::new(new);

        let self_bump = self.bump.get();

        unsafe { new.bump.get().as_ref().set_next(Some(self_bump)) };
        self.bump.set(new.bump.get())
    }
}

impl Chain {
    /// Returns the capacity of this `Chain`.
    /// This is how many *bytes* in total can
    /// be allocated within this `Chain`.
    pub fn capacity(&self) -> usize {
        unsafe { self.bump.get().as_ref().capacity() }
    }

    /// Returns the remaining capacity of this `Chain`.
    /// This is how many more *bytes* can be allocated
    /// within this `Chain`.
    pub fn remaining_capacity(&self) -> usize {
        let index = unsafe { self.bump.get().as_ref().current_index() };

        self.capacity() - index
    }
}

impl Drop for Chain {
    fn drop(&mut self) {
        let mut current = Some(self.bump.get());

        while let Some(non_null) = current {
            unsafe {
                let next = non_null.as_ref().take_next();
                Bump::dealloc(non_null);
                current = next
            }
        }
    }
}
