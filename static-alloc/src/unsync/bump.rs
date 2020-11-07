use core::{
    alloc::{Layout, LayoutErr},
    cell::Cell,
    mem::{self, MaybeUninit},
    ptr::{self, NonNull},
};

use alloc::alloc::{alloc_zeroed, dealloc};
use alloc_traits::AllocTime;

use super::leaked::LeakBox;

pub(crate) type Link = Option<NonNull<Bump>>;

/// A Bump represents an allocation block
/// in which any type can be allocated.
#[repr(C)]
pub struct Bump {
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

impl Bump {
    /// Returns the layout for the `header` of a `Bump`.
    /// The definition of `header` in this case is all the
    /// fields that come **before** the `data` field.
    /// If any of the fields of a Bump are modified,
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

    /// Returns a layout for a Bump where the length of the data field is `size`.
    /// This relies on the two functions defined above.
    pub(crate) fn layout_from_size(size: usize) -> Result<Layout, LayoutErr> {
        let layout = Self::header_layout()?.extend(Self::data_layout(size)?)?.0;
        Ok(layout.pad_to_align())
    }
}

/// The kind of failure while allocation a `Bump`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum Failure {
    RawAlloc,
    Layout,
}

/// A type representing a failure while allocating
/// a `Bump`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub(crate) struct RawAllocError {
    allocation_size: usize,
    kind: Failure,
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

impl Bump {
    /// Given `layout`, allocates a Bump and returns a pointer.
    /// The Bump will be initialized with zeroes.
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
        let size = this.as_ref().capacity();

        let layout =
            Self::layout_from_size(size).expect("Failed to construct layout for allocated Bump");

        dealloc(this.as_ptr() as *mut u8, layout);
    }
}

impl Bump {
    /// Returns capacity of this `Bump`.
    /// This is how many *bytes* can be allocated
    /// within this node.
    pub(crate) const fn capacity(&self) -> usize {
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

    /// Allocates a Bump and returns it.
    pub(crate) fn alloc(size: usize) -> Result<NonNull<Self>, RawAllocError> {
        let layout =
            Self::layout_from_size(size).map_err(|_| RawAllocError::new(size, Failure::Layout))?;

        unsafe {
            let ptr = Self::alloc_raw(layout)?;

            let raw_mut: *mut [Cell<MaybeUninit<u8>>] =
                ptr::slice_from_raw_parts_mut(ptr.cast(), size);
            let node_ptr = raw_mut as *mut Bump;

            Ok(NonNull::new_unchecked(node_ptr))
        }
    }
}

fn next_power_of(n: usize, pow: usize) -> usize {
    let remain = n % pow;

    [n, n + (pow - remain)][(remain != 0) as usize]
}

impl Bump {
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

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd)]
pub struct BumpError<T> {
    val: T,
}

impl<T> BumpError<T> {
    const fn new(val: T) -> Self {
        Self { val }
    }

    pub fn into_inner(self) -> T {
        self.val
    }
}

impl Bump {
    pub(crate) fn push<'node, T>(
        &'node self,
        elem: T,
    ) -> Result<LeakBox<'node, T>, BumpError<T>> {
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


        // `end` should never overflow becouse of the slicing
        // above. If somehow it *does* overflow, saturate at
        // the max value, which is caught in a next `push` call.
        let end = start.saturating_add(mem::size_of::<T>());
        self.index.set(end);

        let lifetime: AllocTime<'node> = AllocTime::default();
        Ok(unsafe {
            LeakBox::new(ptr, elem, lifetime)
        })
    }
}
