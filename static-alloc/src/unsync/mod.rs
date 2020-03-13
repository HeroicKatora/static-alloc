//! This module defines a simple bump allocator.
//! The allocator is not thread safe.

mod node;
mod allocation;

use node::{AllocationError, Node, BumpError};
use allocation::Allocation;

use core::{
    mem::ManuallyDrop,
    ptr::{NonNull},
    cell::Cell,
};

/// A `Bump` is a simple bump allocator, that draws
/// it's memory from another allocator. Bump allocators
/// can be chained together using [`Bump::chain`]. 
pub struct Bump {
    node: Cell<NonNull<Node>>
}

impl Bump {
    /// Creates a new `Bump` that has a capacity of `size`
    /// bytes.
    pub fn new(size: usize) -> Result<Self, AllocationError> {
        Node::alloc(size).map(|node| Self {
            node: Cell::new(node)
        })
    }

    /// Attempts to allocate `elem` within the allocator.
    pub fn alloc<'bump, T>(&'bump self, elem: T) -> Result<Allocation<'bump, T>, BumpError<T>> {
        unsafe {
            let node_ptr = self.node.as_ptr();
            (&*node_ptr).as_ref().push(elem)
        }
    }

    /// Chains `self` together with `new`.
    pub fn chain(&self, new: Bump) {
        let new: ManuallyDrop<_> = ManuallyDrop::new(new);

        let self_node = self.node.get();

        unsafe { new.node.get().as_ref().set_next(Some(self_node)) };
        self.node.set(new.node.get())
    }
}

impl Bump {
    /// Returns the capacity of this `Bump`.
    /// This is how many *bytes* in total can
    /// be allocated within this `Bump`.
    pub fn capacity(&self) -> usize {
        unsafe {
            self.node.get().as_ref().capacity()
        }
    }

    /// Returns the remaining capacity of this `Bump`.
    /// This is how many more *bytes* can be allocated
    /// within this `Bump`.
    pub fn remaining_capacity(&self) -> usize {
        let index = unsafe {
            self.node.get().as_ref().current_index()
        };

        self.capacity() - index
    }
}

impl Drop for Bump {
    fn drop(&mut self) {
        let mut current = Some(self.node.get());

        while let Some(non_null) = current {
            unsafe {
                let next = non_null.as_ref().take_next();
                Node::dealloc(non_null);
                current = next
            }
        }
    }
}