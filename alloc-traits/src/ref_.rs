use core::ptr::{copy_nonoverlapping, write_bytes, NonNull};

use crate::NonZeroLayout;
use crate::LocalAlloc;

/// An allocation without tracked lifetime.
pub struct Allocation {
    ptr: NonNull<u8>,
    layout: NonZeroLayout,
}

/// A references to an allocator.
///
/// Allocations must be live for the lifetime of `self`. That is one must be able to move the
/// `self` and keep all allocations. In particular, a reference to a [`LocalAlloc`] is an
/// `AllocRef`.
///
/// [`LocalAlloc`]: trait.LocalAlloc.html
pub unsafe trait AllocRef {
    /// Allocate one block of memory.
    ///
    /// The callee guarantees that a successful return contains a pointer that is valid for **at
    /// least** the layout requested by the caller.
    fn alloc(&mut self, layout: NonZeroLayout) -> Option<Allocation>;

    /// Deallocate a block previously allocated.
    /// # Safety
    /// The caller must ensure that:
    /// * `alloc` has been previously returned from a call to `alloc`.
    /// * There are no more pointer to the allocation.
    unsafe fn dealloc(&mut self, alloc: Allocation);

    /// Allocate a block of memory initialized with zeros.
    ///
    /// The callee guarantees that a successful return contains a pointer that is valid for **at
    /// least** the layout requested by the caller and the contiguous region of bytes, starting at
    /// the pointer and with the size of the returned layout, is initialized and zeroed.
    fn alloc_zeroed(&mut self, layout: NonZeroLayout)
        -> Option<Allocation> 
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
    unsafe fn realloc(&mut self, alloc: Allocation, layout: NonZeroLayout)
        -> Option<Allocation>
    {
        let new_alloc = self.alloc(layout)?;
        copy_nonoverlapping(
            alloc.ptr.as_ptr(),
            new_alloc.ptr.as_ptr(),
            layout.size().min(alloc.layout.size()).into());
        Some(new_alloc)
    }
}

impl Allocation {
    pub(crate) fn from_local(alloc: crate::local::Allocation) -> Self {
        Allocation {
            ptr: alloc.ptr,
            layout: alloc.layout,
        }
    }

    pub(crate) fn into_local<'lt>(self) -> crate::local::Allocation<'lt> {
        crate::local::Allocation {
            ptr: self.ptr,
            layout: self.layout,
            lifetime: crate::AllocTime::default(),
        }
    }
}

/// Note the 
unsafe impl<'rf, T> AllocRef for &'rf T
    where T: LocalAlloc<'rf>
{
    fn alloc(&mut self, layout: NonZeroLayout) -> Option<Allocation> {
        LocalAlloc::<'rf>::alloc(*self, layout).map(Allocation::from_local)
    }

    unsafe fn dealloc(&mut self, alloc: Allocation) {
        LocalAlloc::<'rf>::dealloc(*self, alloc.into_local())
    }

    fn alloc_zeroed(&mut self, layout: NonZeroLayout)
        -> Option<Allocation> 
    {
        LocalAlloc::<'rf>::alloc_zeroed(*self, layout).map(Allocation::from_local)
    }

    unsafe fn realloc(&mut self, alloc: Allocation, layout: NonZeroLayout)
        -> Option<Allocation>
    {
        LocalAlloc::<'rf>::realloc(*self, alloc.into_local(), layout)
            .map(Allocation::from_local)
    }
}
