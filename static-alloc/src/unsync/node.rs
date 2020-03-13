use core::{
    alloc::{Layout, LayoutErr},
    cell::Cell,
    mem::{self, MaybeUninit},
    ptr::{self, NonNull},
};

use alloc::alloc::{alloc_zeroed, dealloc};

use super::allocation::Allocation;

pub(crate) type Link = Option<NonNull<Node>>;

/// A Node represents an allocation block
/// in which any type can be allocated.
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
    /// Returns the layout for the `header` of a `Node`.
    /// The definition of `header` in this case is all the
    /// fields that come **before** the `data` field.
    /// If any of the fields of a Node are modified,
    /// this function likely has to be modified too.
    fn header_layout() -> Result<Layout, LayoutErr> {
        Layout::new::<Cell<Link>>()
            .extend(Layout::new::<Cell<usize>>())
            .map(|layout| layout.0)
    }

    /// Returns the layout for an array with the size of `size`
    fn data_layout(size: usize) -> Result<Layout, LayoutErr> {
        Layout::new::<Cell<MaybeUninit<u8>>>()
            .repeat(size)
            .map(|layout| layout.0)
    }

    /// Returns a layout for a Node where the length of the data field is `size`.
    /// This relies on the two functions defined above.
    pub(crate) fn layout_from_size(size: usize) -> Result<Layout, LayoutErr> {
        let layout = Self::header_layout()?.extend(Self::data_layout(size)?)?.0;
        Ok(layout.pad_to_align())
    }
}

/// An `AllocFailure` represents failed allocation **of** a Node.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AllocFailure {
    /// The size that could not be allocated
    size: usize,
}

impl AllocFailure {
    fn new(size: usize) -> Self {
        Self { size }
    }
}

/// An `AllocationError` represents a failure during the process
/// of allocating a Node.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AllocationError {
    /// A failed allocation of a Node
    AllocationFailure(AllocFailure),

    /// Anything else that went wrong during the proces
    Other,
}

impl Node {
    /// Given `layout`, allocates a Node and returns a pointer.
    /// The Node will be initialized with zeroes.
    unsafe fn alloc_raw(layout: Layout) -> Result<*mut u8, AllocFailure> {
        let ptr = alloc_zeroed(layout);

        if ptr.is_null() {
            return Err(AllocFailure::new(layout.size()));
        } else {
            Ok(ptr)
        }
    }

    /// Deallocates `this`
    pub(crate) unsafe fn dealloc(this: NonNull<Self>) {
        let size = this.as_ref().capacity();
        let layout = Self::layout_from_size(size).unwrap();

        dealloc(this.as_ptr() as *mut u8, layout);
    }
}

impl Node {
    /// Returns capacity of this `Node`.
    /// This is how many *bytes* can be allocated
    /// within this node.
    pub(crate) fn capacity(&self) -> usize {
        self.data.len()
    }

    pub(crate) fn current_index(&self) -> usize {
        self.index.get()
    }

    pub(crate) fn set_next(&self, next: Link) {
        self.next.set(next);
    }

    pub(crate) fn take_next(&self) -> Link {
        self.next.take()
    }

    /// Allocates a Node and returns it.
    pub(crate) fn alloc(size: usize) -> Result<NonNull<Self>, AllocationError> {
        let layout = Self::layout_from_size(size).map_err(|_| AllocationError::Other)?;

        unsafe {
            let ptr = Self::alloc_raw(layout).map_err(|error| AllocationError::AllocationFailure(error))?;

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

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BumpError<T> {
    val: T
}

impl <T> BumpError<T> {
    fn new(val: T) -> Self {
        Self { val }
    }
}

impl Node {
    pub(crate) fn push<'node, T>(&'node self, elem: T) -> Result<Allocation<'node, T>, BumpError<T>> {
        let start = self.align_index_for::<T>();
        let ptr = match self
            .data
            .get(start..)
            .and_then(|slice| slice.get(..mem::size_of::<T>()))
            .map(|place| {
                let ptr = place.as_ptr() as *mut T;
                assert!(ptr as usize % mem::align_of::<T>() == 0);
                ptr
            }) {
            Some(ptr) => ptr,
            None => return Err(BumpError::new(elem)),
        };

        unsafe {
            ptr.write(elem);
        }

        // `end` should never overflow becouse of the slicing
        // above. If somehow it *does* overflow, saturate at
        // the max value, which is caught in a next `push` call.
        let end = start.saturating_add(mem::size_of::<T>());
        self.index.set(end);
        Ok(Allocation::new(ptr))
    }
}
