//! This module defines a simple bump allocator.
//! The allocator is not thread safe.
use core::{
    alloc::{Layout, LayoutErr},
    cell::Cell,
    mem::{ManuallyDrop, MaybeUninit},
    ptr::{self, NonNull},
};

use alloc::alloc::{alloc_zeroed, dealloc};

use crate::unsync::bump::{MemBump, BumpError};
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

type LinkPtr = Option<NonNull<Link>>;

struct Link {
    /// A pointer to the next node within the list.
    /// This is wrapped in a Cell, so we can modify
    /// this field with just an &self reference.
    next: Cell<LinkPtr>,
    /// The bump allocator of this link.
    bump: MemBump,
}

/// A `Chain` is a simple bump allocator, that draws
/// it's memory from another allocator. Chain allocators
/// can be chained together using [`Chain::chain`].
pub struct Chain {
    root: Cell<NonNull<Link>>,
}

impl Chain {
    /// Creates a new `Chain` that has a capacity of `size`
    /// bytes.
    pub fn new(size: usize) -> Result<Self, TryNewError> {
        let link = Link::alloc(size).map_err(|e| TryNewError { inner: e })?;
        Ok(Chain {
            root: Cell::new(link),
        })
    }

    /// Attempts to allocate `elem` within the allocator.
    pub fn try_alloc<'bump, T>(&'bump self, elem: T) -> Result<LeakBox<'bump, T>, BumpError<T>> {
        self.root().as_bump().push(elem)
    }

    /// Chains `self` together with `new`.
    pub fn chain(&self, new: Chain) {
        let new: ManuallyDrop<_> = ManuallyDrop::new(new);

        let self_bump = self.root.get();
        new.root().set_next(Some(self_bump));

        self.root.set(new.root.get())
    }

    /// Returns the capacity of this `Chain`.
    /// This is how many *bytes* in total can
    /// be allocated within this `Chain`.
    pub fn capacity(&self) -> usize {
        self.root().as_bump().capacity()
    }

    /// Returns the remaining capacity of this `Chain`.
    /// This is how many more *bytes* can be allocated
    /// within this `Chain`.
    pub fn remaining_capacity(&self) -> usize {
        let index = self.root().as_bump().current_index();
        self.capacity() - index
    }

    fn root(&self) -> &Link {
        unsafe {
            let bump_ptr = self.root.as_ptr();
            (*bump_ptr).as_ref()
        }
    }
}

/// The kind of failure while allocation a `MemBump`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum Failure {
    RawAlloc,
    Layout,
}

/// A type representing a failure while allocating
/// a `MemBump`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub(crate) struct RawAllocError {
    allocation_size: usize,
    kind: Failure,
}

impl Link {
    pub(crate) fn set_next(&self, next: LinkPtr) {
        self.next.set(next);
    }

    pub(crate) fn take_next(&self) -> LinkPtr {
        self.next.take()
    }

    pub(crate) fn as_bump(&self) -> &MemBump {
        &self.bump
    }

    pub(crate) fn layout_from_size(size: usize) -> Result<Layout, LayoutErr> {
        Layout::new::<Cell<LinkPtr>>()
            .extend(MemBump::layout_from_size(size)?)
            .map(|layout| layout.0)
    }

    /// Given `layout`, allocates a MemBump and returns a pointer.
    /// The MemBump will be initialized with zeroes.
    unsafe fn alloc_raw(layout: Layout) -> Result<*mut u8, RawAllocError> {
        let ptr = alloc_zeroed(layout);

        if ptr.is_null() {
            return Err(RawAllocError::new(layout.size(), Failure::RawAlloc));
        } else {
            Ok(ptr)
        }
    }

    /// Deallocates `this`
    pub(crate) unsafe fn dealloc(this: NonNull<Self>) {
        let size = this.as_ref().as_bump().capacity();

        let layout =
            Self::layout_from_size(size).expect("Failed to construct layout for allocated MemBump");

        dealloc(this.as_ptr() as *mut u8, layout);
    }

    /// Allocates a MemBump and returns it.
    pub(crate) fn alloc(size: usize) -> Result<NonNull<Self>, RawAllocError> {
        let layout =
            Self::layout_from_size(size).map_err(|_| RawAllocError::new(size, Failure::Layout))?;

        unsafe {
            let ptr = Self::alloc_raw(layout)?;

            let raw_mut: *mut [Cell<MaybeUninit<u8>>] =
                ptr::slice_from_raw_parts_mut(ptr.cast(), size);
            let node_ptr = raw_mut as *mut Link;

            Ok(NonNull::new_unchecked(node_ptr))
        }
    }
}

impl RawAllocError {
    const fn new(allocation_size: usize, kind: Failure) -> Self {
        Self {
            allocation_size,
            kind,
        }
    }

    pub(crate) const fn allocation_size(&self) -> usize {
        self.allocation_size
    }
}

impl Drop for Chain {
    fn drop(&mut self) {
        let mut current = Some(self.root.get());

        while let Some(non_null) = current {
            unsafe {
                let next = non_null.as_ref().take_next();
                Link::dealloc(non_null);
                current = next
            }
        }
    }
}
