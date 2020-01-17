//! Traits to replace or supplement the alloc module in `no_std`.
//! 
//! Defines traits, similar to `alloc::GlobalAlloc`, that can be implemented to defined different
//! kinds of allocators. Unlike the standard library one they do not presume global uniqueness and
//! static lifetime of the memory resource provider. In return, the allocators are not required to
//! implement the `Sync` bound and can easily be built without operating system support to be
//! usable.
//! 
//! There are additional independent crates with additional abstractions on-top:
//! * [`static-alloc`]: A simple allocator drawing from a memory region statically
//!   embedded within the compiled binary.
//! * [`alloc-free`]: A set of data structures (`Box`, `Vec`, `Rc`, ...) that can
//!   be allocated from the implementors of the traits defined here.
//! 
//! [`static-alloc`]: https://crates.io/crates/static-alloc
//! [`alloc-free`]: https://crates.io/crates/alloc-free

// Copyright 2019 Andreas Molzer
#![no_std]
#![deny(missing_docs)]

mod layout;

use core::fmt;
use core::marker::PhantomData;
use core::ptr::{copy_nonoverlapping, write_bytes, NonNull};

pub use layout::{Layout, NonZeroLayout};

/// A marker struct denoting a lifetime that is not simply coercible to another.
#[derive(Clone, Copy, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct AllocTime<'lt> {
    marker: PhantomData<&'lt fn(&'lt ())>,
}

/// A marker struct denoting a lifetime that is not simply coercible to another.
#[deprecated = "Use the new name 'AllocTime' instead"]
pub type Invariant<'lt> = AllocTime<'lt>;

/// An allocation valid for a particular lifetime.
///
/// It is advisable to try and deallocate it before the end of the lifetime instead of leaking the
/// allocation.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Allocation<'alloc> {
    /// A pointer to the allocated and potentially uninitialized bytes.
    pub ptr: NonNull<u8>,
    /// The allocated layout.
    pub layout: NonZeroLayout,
    /// The lifetime of the allocation.
    pub lifetime: AllocTime<'alloc>,
}

/// An allocator providing memory regions valid for a particular lifetime.
///
/// It is useful to compare this trait to `std::alloc::GlobalAlloc`. Similar to the trait it is
/// required that the implementors adhere to the contract of the methods.
pub unsafe trait LocalAlloc<'alloc> {
    /// Allocate one block of memory.
    ///
    /// The callee guarantees that a successful return contains a pointer that is valid for **at
    /// least** the layout requested by the caller.
    fn alloc(&'alloc self, layout: NonZeroLayout) -> Option<Allocation<'alloc>>;

    /// Deallocate a block previously allocated.
    /// # Safety
    /// The caller must ensure that:
    /// * `alloc` has been previously returned from a call to `alloc`.
    /// * There are no more pointer to the allocation.
    unsafe fn dealloc(&'alloc self, alloc: Allocation<'alloc>);

    /// Allocate a block of memory initialized with zeros.
    ///
    /// The callee guarantees that a successful return contains a pointer that is valid for **at
    /// least** the layout requested by the caller and the contiguous region of bytes, starting at
    /// the pointer and with the size of the returned layout, is initialized and zeroed.
    fn alloc_zeroed(&'alloc self, layout: NonZeroLayout)
        -> Option<Allocation<'alloc>> 
    {
        let allocation = self.alloc(layout)?;
        unsafe {
            write_bytes(allocation.ptr.as_ptr(), 0u8, allocation.layout.size().into());
        }
        Some(allocation)
    }

    /// Change the layout of a block previously allocated.
    ///
    /// The callee guarantees that a successful return contains a pointer that is valid for **at
    /// least** the layout requested by the caller and the contiguous region of bytes, starting at
    /// the pointer and with the size of the returned layout, is initialized with the prefix of the
    /// previous allocation that is still valid.
    unsafe fn realloc(&'alloc self, alloc: Allocation<'alloc>, layout: NonZeroLayout)
        -> Option<Allocation<'alloc>>
    {
        let new_alloc = self.alloc(layout)?;
        copy_nonoverlapping(
            alloc.ptr.as_ptr(),
            new_alloc.ptr.as_ptr(),
            layout.size().min(alloc.layout.size()).into());
        Some(new_alloc)
    }
}

impl fmt::Debug for AllocTime<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("AllocTime")
    }
}
