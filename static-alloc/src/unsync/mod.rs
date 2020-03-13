/// This module defines a simple bump allocator.
/// The allocator is not thread safe.
mod node;
mod allocation;

use node::Node;
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
    pub fn new(size: usize) -> Result<Self, ()> {
        Node::new(size).map(|node| Self {
            node: Cell::new(node)
        })
    }

    /// Attempts to allocate `elem` within the allocator.
    pub fn alloc<'bump, T>(&'bump self, elem: T) -> Result<Allocation<'bump, T>, T> {
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

#[cfg(test)]
mod tests {
    use super::Bump;
    //#[test]
    fn unsync_bump() {
        let mut bump = Bump::new(20).unwrap();

        let mut n1 = bump.alloc(10usize).unwrap();
        let mut n2 = bump.alloc(20usize).unwrap();
        let mut n3 = bump.alloc(10i32).unwrap();

        assert!(bump.alloc(10usize).is_err())
    }
}