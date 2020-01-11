#![cfg_attr(not(test), no_std)]
#[cfg(test)]
extern crate alloc;

mod layout;
#[cfg(test)]
mod global;

use core::fmt;
use core::marker::PhantomData;
use core::ptr::{copy_nonoverlapping, write_bytes, NonNull};

pub use layout::{Layout, NonZeroLayout};

#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Invariant<'lt> {
    marker: PhantomData<&'lt fn(&'lt ())>,
}

pub struct Global;

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
    pub lifetime: Invariant<'alloc>,
}

pub trait LocalAlloc<'alloc> {
    /// Allocate one block of memory.
    /// # Safety
    /// The caller must ensure that:
    fn alloc(&'alloc self, layout: NonZeroLayout) -> Option<Allocation<'alloc>>;

    /// Deallocate a block previously allocated.
    /// # Safety
    /// The caller must ensure that:
    /// * `alloc` has been previously returned from a call to `alloc`.
    /// * There are no more pointer to the allocation.
    unsafe fn dealloc(&'alloc self, alloc: Allocation<'alloc>);

    unsafe fn alloc_zeroed(&'alloc self, layout: NonZeroLayout)
        -> Option<Allocation<'alloc>> 
    {
        let allocation = self.alloc(layout)?;
        write_bytes(allocation.ptr.as_ptr(), 0u8, allocation.layout.size().into());
        Some(allocation)
    }

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

impl fmt::Debug for Invariant<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("Invariant")
    }
}
