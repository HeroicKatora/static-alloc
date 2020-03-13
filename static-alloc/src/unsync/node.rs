use core::{
    alloc::{Layout, LayoutErr},
    cell::Cell,
    mem::{self, MaybeUninit},
    ptr::{self, NonNull},
};

use alloc::alloc::{alloc_zeroed, dealloc};

use super::allocation::Allocation;

pub(crate) type Link = Option<NonNull<Node>>;

/// A Node represents an allocation block within
/// the arena allocator.
#[repr(C)]
pub struct Node {
    /// A pointer to the next node within the list.
    /// This is wrapped in a Cell, so we can modify
    /// this field with just an &self reference.
    next: Cell<Link>,

    /// An index into the data field. This index
    /// will always be an index to an element
    /// that has not been allocated into.
    /// Again this is wrapped in a Cell,
    /// to allow modification with just a
    /// &self reference.
    index: Cell<usize>,

    /// The data slice of a node. This slice
    /// may be of any arbitrary size. We use
    /// a Cell<MaybeUninit> to allow modification
    /// trough a &self reference, and to allow
    /// writing uninit padding bytes.
    data: [Cell<MaybeUninit<u8>>],
}

impl Node {
    fn header_layout() -> Result<Layout, LayoutErr> {
        Layout::new::<Cell<Link>>()
            .extend(Layout::new::<Cell<usize>>())
            .map(|layout| layout.0)
    }

    fn data_layout(size: usize) -> Result<Layout, LayoutErr> {
        Layout::new::<Cell<MaybeUninit<u8>>>()
            .repeat(size)
            .map(|layout| layout.0)
    }

    pub(crate) fn layout_from_size(size: usize) -> Result<Layout, LayoutErr> {
        let layout = Self::header_layout()?.extend(Self::data_layout(size)?)?.0;
        Ok(layout.pad_to_align())
    }
}

impl Node {
    unsafe fn alloc(layout: Layout) -> Result<*mut u8, ()> {
        let ptr = alloc_zeroed(layout);

        if ptr.is_null() {
            return Err(());
        } else {
            Ok(ptr)
        }
    }

    pub(crate) unsafe fn dealloc(this: NonNull<Self>) {
        let size = this.as_ref().capacity();
        let layout = Self::layout_from_size(size).unwrap();

        dealloc(this.as_ptr() as *mut u8, layout);
    }
}

impl Node {
    pub(crate) fn capacity(&self) -> usize {
        self.data.len()
    }

    pub(crate) fn set_next(&self, next: Link) {
        self.next.set(next);
    }

    pub(crate) fn take_next(&self) -> Link {
        self.next.take()
    }

    pub(crate) fn new(size: usize) -> Result<NonNull<Self>, ()> {
        let layout = Self::layout_from_size(size).map_err(drop)?;

        unsafe {
            let ptr = Self::alloc(layout)?;

            let raw_mut: *mut [Cell<MaybeUninit<u8>>] =
                ptr::slice_from_raw_parts_mut(ptr.cast(), size);
            let node_ptr = raw_mut as *mut Node;

            Ok(NonNull::new_unchecked(node_ptr))
        }
    }
}

fn next_power_of(n: usize, pow: usize) -> usize {
    let remain = n % pow;

    [n, n + (pow - remain)][(remain != 0) as usize]
}

impl Node {
    /// Returns the start *address* of the data field
    fn data_start_address(&self) -> usize {
        self.data.as_ptr() as usize + self.index.get()
    }

    fn align_index_for<T>(&self) -> usize {
        let start_addr = self.data_start_address();
        let aligned_start = next_power_of(start_addr, mem::align_of::<T>());
        let aligned_index = aligned_start - self.data.as_ptr() as usize;
        aligned_index
    }
}

impl Node {
    // TODO: Differentiate between an OOM failure, and an error
    // that *this* node doesnt have sufficient capacity for T.
    pub(crate) fn push<'node, T>(&'node self, elem: T) -> Result<Allocation<'node, T>, T> {
        let start = self.align_index_for::<T>();
        let end = start + mem::size_of::<T>();

        unsafe {
            assert!(self.data.as_ptr().offset(start as isize) as usize % mem::align_of::<T>() == 0);
        }

        if end > self.capacity() {
            return Err(elem);
        }

        let ptr: *mut T = self.data[start..end].as_ptr() as _;

        unsafe {
            ptr.write(elem);
        }

        self.index.set(end);
        Ok(Allocation::new(ptr))
    }
}
