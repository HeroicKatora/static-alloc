use core::{
    alloc::{Layout, LayoutErr},
    cell::{Cell, UnsafeCell},
    mem::{self, MaybeUninit},
    ops,
    ptr::{self, NonNull},
};

use alloc_traits::AllocTime;

use crate::bump::{Allocation, Failure, Level};
use crate::leaked::LeakBox;

/// A bump allocator whose storage capacity and alignment is given by `T`.
///
/// This type dereferences to the generic `MemBump` that implements the allocation behavior. Note
/// that `MemBump` is an unsized type. In contrast this type is sized so it is possible to
/// construct an instance on the stack or leak one from another bump allocator such as a global
/// one.
///
/// # Usage
///
/// ```
/// ```
#[repr(C)]
pub struct Bump<T> {
    /// The index used in allocation.
    _index: Cell<usize>,
    /// The backing storage for raw allocated data.
    _data: UnsafeCell<MaybeUninit<T>>,
    // Warning: when changing the data layout, you must change `MemBump` as well.
}

/// A dynamically sized allocation block in which any type can be allocated.
#[repr(C)]
pub struct MemBump {
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
    /// Note that the underlying memory is in one
    /// contiguous `UnsafeCell`, it's only represented
    /// here to make it easier to slice.
    data: [UnsafeCell<MaybeUninit<u8>>],
}

impl<T> Bump<T> {
    /// Create an allocator with uninitialized memory.
    ///
    /// All allocations coming from the allocator will need to be initialized manually.
    pub fn uninit() -> Self {
        Bump {
            _index: Cell::new(0),
            _data: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Create an allocator with zeroed memory.
    ///
    /// The caller can rely on all allocations to be zeroed.
    pub fn zeroed() -> Self {
        Bump {
            _index: Cell::new(0),
            _data: UnsafeCell::new(MaybeUninit::zeroed()),
        }
    }
}

impl MemBump {
    /// Returns the layout for the `header` of a `MemBump`.
    /// The definition of `header` in this case is all the
    /// fields that come **before** the `data` field.
    /// If any of the fields of a MemBump are modified,
    /// this function likely has to be modified too.
    fn header_layout() -> Layout {
        Layout::new::<Cell<usize>>()
    }

    /// Returns the layout for an array with the size of `size`
    fn data_layout(size: usize) -> Result<Layout, LayoutErr> {
        Layout::array::<Cell<MaybeUninit<u8>>>(size)
    }

    /// Returns a layout for a MemBump where the length of the data field is `size`.
    /// This relies on the two functions defined above.
    pub(crate) fn layout_from_size(size: usize) -> Result<Layout, LayoutErr> {
        let data_tail = Self::data_layout(size)?;
        let (layout, _) = Self::header_layout().extend(data_tail)?;
        Ok(layout.pad_to_align())
    }
}

impl MemBump {
    /// Returns capacity of this `MemBump`.
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

impl MemBump {
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

    /// Allocate a region of memory.
    ///
    /// This is a safe alternative to [GlobalAlloc::alloc](#impl-GlobalAlloc).
    ///
    /// # Panics
    /// This function will panic if the requested layout has a size of `0`. For the use in a
    /// `GlobalAlloc` this is explicitely forbidden to request and would allow any behaviour but we
    /// instead strictly check it.
    pub fn alloc(&self, layout: Layout) -> Option<NonNull<u8>> {
        Some(self.try_alloc(layout)?.ptr)
    }

    /// Try to allocate some layout with a precise base location.
    ///
    /// The base location is the currently consumed byte count, without correction for the
    /// alignment of the allocation. This will succeed if it can be allocate exactly at the
    /// expected location.
    ///
    /// # Panics
    /// This function may panic if the provided `level` is from a different slab.
    pub fn alloc_at(&self, layout: Layout, level: Level)
        -> Result<NonNull<u8>, Failure>
    {
        let Allocation { ptr, .. } = self.try_alloc_at(layout, level.0)?;
        Ok(ptr)
    }

    pub fn get<V>(&self) -> Option<Allocation<V>> {
        todo!()
    }

    pub fn get_at<V>(&self, level: Level) -> Result<Allocation<V>, Failure> {
        todo!()
    }

    pub fn bump_box<T>(&self) -> Result<LeakBox<'_, MaybeUninit<T>>, Failure> {
        todo!()
    }

    pub fn bump_array<T>(&self, n: usize) -> Result<&'_ mut [MaybeUninit<T>], Failure> {
        let layout = Layout::array::<T>(n).map_err(|_| Failure::Exhausted)?;
        let raw = self.alloc(layout).ok_or(Failure::Exhausted)?;
        Ok(unsafe {
            &mut *(ptr::slice_from_raw_parts_mut(raw.cast().as_ptr(), n))
        })
    }

    pub fn level(&self) -> Level {
        todo!()
    }

    fn try_alloc(&self, layout: Layout)
        -> Option<Allocation<'_>>
    {
        let consumed = self.index.get();
        match self.try_alloc_at(layout, consumed) {
            Ok(alloc) => return Some(alloc),
            Err(Failure::Exhausted) => return None,
            Err(Failure::Mismatch{ observed: _ }) => {
                unreachable!("Count in Cell concurrently modified, this UB")
            }
        }
    }

    fn try_alloc_at(&self, layout: Layout, expect_consumed: usize)
        -> Result<Allocation<'_>, Failure>
    {
        assert!(layout.size() > 0);
        let length = layout.size();
        // We want to access contiguous slice, so cast to a single cell.
        let data: &UnsafeCell<[MaybeUninit<u8>]> =
            unsafe { &*(&self.data as *const _ as *const UnsafeCell<_>) };
        let base_ptr = data.get() as *mut u8;

        let alignment = layout.align();
        let requested = layout.size();

        // Ensure no overflows when calculating offets within.
        assert!(expect_consumed <= length);

        let available = length.checked_sub(expect_consumed).unwrap();
        let ptr_to = base_ptr.wrapping_add(expect_consumed);
        let offset = ptr_to.align_offset(alignment);

        if requested > available.saturating_sub(offset) {
            return Err(Failure::Exhausted); // exhausted
        }

        // `size` can not be zero, saturation will thus always make this true.
        assert!(offset < available);
        let at_aligned = expect_consumed.checked_add(offset).unwrap();
        let new_consumed = at_aligned.checked_add(requested).unwrap();
        // new_consumed
        //    = consumed + offset + requested  [lines above]
        //   <= consumed + available  [bail out: exhausted]
        //   <= length  [first line of loop]
        // So it's ok to store `allocated` into `consumed`.
        assert!(new_consumed <= length);
        assert!(at_aligned < length);

        // Try to actually allocate.
        match self.bump(expect_consumed, new_consumed) {
            Ok(()) => (),
            Err(observed) => {
                // Someone else was faster, if you want it then recalculate again.
                return Err(Failure::Mismatch { observed: Level(observed) });
            },
        }

        let aligned = unsafe {
            // SAFETY:
            // * `0 <= at_aligned < length` in bounds as checked above.
            (base_ptr as *mut u8).add(at_aligned)
        };

        Ok(Allocation {
            ptr: NonNull::new(aligned).unwrap(),
            lifetime: AllocTime::default(),
            level: Level(new_consumed),
        })
    }

    fn bump(&self, expect: usize, consume: usize) -> Result<(), usize> {
        debug_assert!(consume <= self.capacity());
        debug_assert!(expect <= consume);
        let prev = self.index.get();
        if prev != expect {
            Err(prev)
        } else {
            self.index.set(consume);
            Ok(())
        }
    }

    /// 'Allocate' a ZST.
    fn zst_fake_alloc<Z>(&self) -> Allocation<'_, Z> {
        Allocation::for_zst(self.level())
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

impl<T> ops::Deref for Bump<T> {
    type Target = MemBump;
    fn deref(&self) -> &MemBump {
        let from_layout = Layout::for_value(self);
        let data_layout = Layout::new::<MaybeUninit<T>>();
        // Construct a point with the meta data of a slice to `data`, but pointing to the whole
        // struct instead. This meta data is later copied to the meta data of `bump` when cast.
        let ptr = self as *const Self as *const MaybeUninit<u8>;
        let mem: *const [MaybeUninit<u8>] =
            ptr::slice_from_raw_parts(ptr, data_layout.size());
        // Now we have a pointer to MemBump with length meta data of the data slice.
        let bump = unsafe { &*(mem as *const MemBump) };
        debug_assert_eq!(from_layout, Layout::for_value(bump));
        bump
    }
}

#[test]
fn mem_bump_derefs_correctly() {
    let bump = Bump::<usize>::zeroed();
    let mem: &MemBump = &bump;
    assert_eq!(mem::size_of_val(&bump), mem::size_of_val(mem));
}
