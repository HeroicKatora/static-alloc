use core::{
    alloc::{Layout, LayoutErr},
    cell::Cell,
    mem::{self, MaybeUninit},
    ptr::NonNull,
};

use alloc_traits::AllocTime;

use crate::leaked::LeakBox;

/// A Bump represents an allocation block
/// in which any type can be allocated.
#[repr(C)]
pub struct Bump {
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
    fn header_layout() -> Layout {
        Layout::new::<Cell<usize>>()
    }

    /// Returns the layout for an array with the size of `size`
    fn data_layout(size: usize) -> Result<Layout, LayoutErr> {
        Layout::array::<Cell<MaybeUninit<u8>>>(size)
    }

    /// Returns a layout for a Bump where the length of the data field is `size`.
    /// This relies on the two functions defined above.
    pub(crate) fn layout_from_size(size: usize) -> Result<Layout, LayoutErr> {
        let data_tail = Self::data_layout(size)?;
        let (layout, _) = Self::header_layout().extend(data_tail)?;
        Ok(layout.pad_to_align())
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
                // TODO: use NonNull<[u8]>::as_non_null_ptr().cast()
                // as soon as `slice_ptr_get` is stable
                ptr
            }) {
            Some(ptr) => ptr,
            None => return Err(BumpError::new(elem)),
        };

        debug_assert!(!ptr.is_null());
        let ptr = NonNull::new(ptr).unwrap();
        // `end` should never overflow becouse of the slicing
        // above. If somehow it *does* overflow, saturate at
        // the max value, which is caught in a next `push` call.
        let end = start.saturating_add(mem::size_of::<T>());
        self.index.set(end);

        let lifetime: AllocTime<'node> = AllocTime::default();
        Ok(unsafe {
            LeakBox::new_from_raw_non_null(ptr, elem, lifetime)
        })
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
