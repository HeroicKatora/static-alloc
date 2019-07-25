use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;
use core::mem::{self, MaybeUninit};
use core::ptr::{self, NonNull, null_mut};
use core::sync::atomic::{AtomicUsize, Ordering};

/// An allocator whose memory resource has static storage duration.
///
/// The type parameter `T` is used only to annotate the required size and alignment of the region
/// and has no futher use. Note that in particular there is no safe way to retrieve or unwrap an
/// inner instance even if the `Slab` was not constructed as a shared global static. Nevertheless,

///
/// ## Usage as global allocator
///
/// You can use the stable rust attribute to use an instance of this type as the global allocator.
///
/// ```rust,no_run
/// use static_alloc::Slab;
///
/// #[global_allocator]
/// static A: Slab<[u8; 1 << 16]> = Slab::uninit();
///
/// fn main() { }
/// ```
///
/// Take care, some runtime features of Rust will allocator some memory before or after your own
/// code. In particular, it was found to be be tricky to find out more on the usage of the builtin
/// test framework which seemingly allocates some structures per test.
///
/// ## Usage as a non-dropping local allocator
///
/// It is also possible to use a `Slab` as a stack local allocator or a specialized allocator. The
/// interface offers some utilities for allocating values from references to shared or unshared
/// instances directly. **Note**: this will never call the `Drop` implementation of the allocated
/// type. In particular, it would almost surely not be safe to `Pin` the values.
///
/// ```rust
/// use static_alloc::Slab;
///
/// let local: Slab<[u64; 3]> = Slab::uninit();
///
/// let one = local.leak(0_u64).unwrap();
/// let two = local.leak(1_u64).unwrap();
/// let three = local.leak(2_u64).unwrap();
///
/// // Exhausted the space.
/// assert!(local.leak(3_u64).is_err());
/// ```
///
/// Mind that the supplied type parameter influenced *both* size and alignment and a `[u8; 24]`
/// does not guarantee being able to allocation three `u64` even though most targets have a minimum
/// alignment requirement of 16 and it works fine on those.
///
/// ```rust
/// # use static_alloc::Slab;
/// // Just enough space for `u128` but no alignment requirement.
/// let local: Slab<[u8; 16]> = Slab::uninit();
///
/// // May or may not return an err.
/// let _ = local.leak(0_u128);
/// ```
///
/// Instead use the type parameter to `Slab` as a hint for the best alignment.
///
/// ```rust
/// # use static_alloc::Slab;
/// // Enough space and align for `u128`.
/// let local: Slab<[u128; 1]> = Slab::uninit();
///
/// assert!(local.leak(0_u128).is_ok());
/// ```
///
/// ## Usage as a (local) bag of bits
///
/// It is of course entirely possible to use a local instance instead of a single global allocator.
/// For example you could utilize the pointer interface directly to build a `#[no_std]` dynamic
/// data structure in an environment without `extern lib alloc`. This feature was the original
/// motivation behind the crate but no such data structures are provided here so a quick sketch of
/// the idea must do:
///
/// ```
/// use core::alloc;
/// use static_alloc::Slab;
///
/// #[repr(align(4096))]
/// struct PageTable {
///     // some non-trivial type.
/// #   _private: [u8; 4096],
/// }
///
/// impl PageTable {
///     pub unsafe fn new(into: *mut u8) -> &'static mut Self {
///         // ...
/// #       &mut *(into as *mut Self)
///     }
/// }
///
/// // Allocator for pages for page tables. Provides 64 pages. When the
/// // program/kernel is provided as an ELF the bootloader reserves
/// // memory for us as part of the loading process that we can use
/// // purely for page tables. Replaces asm `paging: .BYTE <size>;`
/// static Paging: Slab<[u8; 1 << 18]> = Slab::uninit();
///
/// fn main() {
///     let layout = alloc::Layout::new::<PageTable>();
///     let memory = Paging.alloc(layout).unwrap();
///     let table = unsafe {
///         PageTable::new(memory.as_ptr())
///     };
/// }
/// ```
///
/// A similar structure would of course work to allocate some non-`'static' objects from a
/// temporary `Slab`.
///
/// ## More insights
///
/// WIP: slices.
pub struct Slab<T> {
    /// An monotonic atomic counter of consumed bytes.
    ///
    /// It is only mutably accessed in `bump` which guarantees its invariants.
    consumed: AtomicUsize,

    /// Outer unsafe cell due to thread safety.
    /// Inner MaybeUninit because we padding may destroy initialization invariant
    /// on the bytes themselves, and hence drop etc must not assumed inited.
    storage: UnsafeCell<MaybeUninit<T>>,
}

/// Could not move a value into an allocation.
#[derive(Debug)]
pub struct NewError<T> {
    val: T,
}

enum NewAllocation {
    Ok {
        /// Pointer to the region with specified layout.
        ptr: NonNull<u8>,

        /// The new number of consumed bytes.
        _consumed: usize,
    },

    /// No space left for that allocation.
    Exhausted,

    /// The allocation would not have used the expected base location.
    ///
    /// Reports the location that was observed.
    Mismatch {
        observed: usize,
    },
}

impl<T> Slab<T> {
    /// Make a new allocatable slab of certain byte size and alignment.
    ///
    /// The storage will contain uninitialized bytes.
    pub const fn uninit() -> Self {
        Slab {
            consumed: AtomicUsize::new(0),
            storage: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Make a new allocatable slab of certain byte size and alignment.
    ///
    /// The storage will contain zeroed bytes. This is not *yet* available
    /// as a `const fn` which currently limits its potential usefulness
    /// but there is no good reason not to provide it regardless.
    pub fn zeroed() -> Self {
        Slab {
            consumed: AtomicUsize::new(0),
            storage: UnsafeCell::new(MaybeUninit::zeroed()),
        }
    }

    /// Make a new allocatable slab provided with some bytes it can hand out.
    ///
    /// Note that `storage` will never be dropped and there is no way to get it back.
    pub const fn new(storage: T) -> Self {
        Slab {
            consumed: AtomicUsize::new(0),
            storage: UnsafeCell::new(MaybeUninit::new(storage)),
        }
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
        assert!(layout.size() > 0, "Violated allocation requirement: Requested region of size 0");

        // Guess zero, this will fail when we try to access it and it isn't.
        let mut consumed = 0;
        loop {
            match self.try_alloc(layout, consumed) {
                NewAllocation::Ok { ptr, .. } => return Some(ptr),
                NewAllocation::Exhausted => return None,
                NewAllocation::Mismatch{ observed } => consumed = observed,
            }
        }
    }

    /// Try to allocate some layout with a precise base location.
    ///
    /// The base location is the currently consumed byte count, without correction for the
    /// alignment of the allocation. This will succeed if it can be allocate exactly at the
    /// expected location.
    ///
    /// # Panics
    /// This function panics if `expect_consumed` is larger than `length`.
    fn try_alloc(&self, layout: Layout, expect_consumed: usize) -> NewAllocation {
        assert!(layout.size() > 0);
        let length = mem::size_of::<T>();
        let base_ptr = self.storage.get()
            as *mut T
            as *mut u8;

        let alignment = layout.align();
        let requested = layout.size();

        // Ensure no overflows when calculating offets within.
        assert!(expect_consumed <= length);

        let available = length.checked_sub(expect_consumed).unwrap();
        let ptr_to = base_ptr.wrapping_add(expect_consumed);
        let offset = ptr_to.align_offset(alignment);

        if requested > available.saturating_sub(offset) {
            return NewAllocation::Exhausted; // exhausted
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
                return NewAllocation::Mismatch { observed };
            },
        }

        let aligned = unsafe {
            // SAFETY:
            // * `0 <= at_aligned < length` in bounds as checked above.
            (base_ptr as *mut u8).add(at_aligned)
        };

        NewAllocation::Ok {
            ptr: NonNull::new(aligned).unwrap(),
            _consumed: new_consumed,
        }
    }

    /// Allocate a value for the lifetime of the allocator.
    ///
    /// The value is leaked in the sense that
    ///
    /// 1. the drop implementation of the allocated value is never called;
    /// 2. reusing the memory for another allocation in the same `Slab` requires manual unsafe code
    ///    to handle dropping and reinitialization.
    ///
    /// However, it does not mean that the underlying memory used for the allocated value is never
    /// reclaimed. If the `Slab` itself is a stack value then it will get reclaimed together with
    /// it.
    ///
    /// ## Safety notice
    ///
    /// It is important to understand that it is undefined behaviour to reuse the allocation for
    /// the *whole lifetime* of the returned reference. That is, dropping the allocation in-place
    /// while the reference is still within its lifetime comes with the exact same unsafety caveats
    /// as [`ManuallyDrop::drop`].
    ///
    /// ```
    /// # use static_alloc::Slab;
    /// #[derive(Debug, Default)]
    /// struct FooBar {
    ///     // ...
    /// # _private: [u8; 1],
    /// }
    ///
    /// let local: Slab<[FooBar; 3]> = Slab::uninit();
    /// let one = local.leak(FooBar::default()).unwrap();
    ///
    /// // Dangerous but justifiable.
    /// let one = unsafe {
    ///     // Ensures there is no current mutable borrow.
    ///     core::ptr::drop_in_place(&mut *one);
    /// };
    /// ```
    ///
    /// ## Usage
    ///
    /// ```
    /// use static_alloc::Slab;
    ///
    /// let local: Slab<[u64; 3]> = Slab::uninit();
    ///
    /// let one = local.leak(0_u64).unwrap();
    /// assert_eq!(*one, 0);
    /// *one = 42;
    /// ```
    ///
    /// ## Limitations
    ///
    /// Only sized values can be allocated in this manner for now, unsized values are blocked on
    /// stabilization of [`ptr::slice_from_raw_parts`]. We can not otherwise get a fat pointer to
    /// the allocated region.
    ///
    /// [`ptr::slice_from_raw_parts`]: https://github.com/rust-lang/rust/issues/36925
    /// [`ManuallyDrop::drop`]: https://doc.rust-lang.org/beta/std/mem/struct.ManuallyDrop.html#method.drop
    pub fn leak<V>(&self, val: V) -> Result<&mut V, NewError<V>> {
        let ptr = if mem::size_of::<V>() == 0 {
            let ptr = NonNull::<V>::dangling().as_ptr();
            // SAFETY: RawVec does this as well. Probably safe, only zero offsets in gep-inbounds.
            // See https://github.com/rust-lang/unsafe-code-guidelines/issues/93
            return Ok(unsafe { &mut *ptr })
        } else {
            match self.alloc(Layout::new::<V>()) {
                Some(ptr) => ptr.as_ptr() as *mut V,
                None => return Err(NewError::new(val)),
            }
        };

        unsafe {
            // SAFETY: ptr is valid for write, non-null, aligned according to V's layout.
            ptr::write(ptr, val);
            // SAFETY: ptr points into `self`, and reference is unique.
            Ok(&mut *ptr)
        }
    }

    /// Try to bump the monotonic, atomic consume counter.
    ///
    /// This is the only place modifying `self.consumed`.
    ///
    /// Returns `Ok` if the consume counter was as expected. Monotonicty and atomicity guarantees
    /// to the caller that no overlapping range can succeed as well. This allocates the range to
    /// the caller.
    ///
    /// Returns the observed consume counter in an `Err` if it was not as expected.
    ///
    /// ## Panics
    /// This function panics if either argument exceeds the byte length of the underlying memory.
    /// It also panics if the expected value is larger than the new value.
    fn bump(&self, expect_consumed: usize, new_consumed: usize) -> Result<(), usize> {
        assert!(expect_consumed <= new_consumed);
        assert!(new_consumed <= mem::size_of::<T>());

        let observed = self.consumed.compare_and_swap(
            expect_consumed,
            new_consumed,
            Ordering::SeqCst);
        if expect_consumed == observed {
            Ok(())
        } else {
            Err(observed)
        }
    }
}

impl<T> NewError<T> {
    pub fn new(val: T) -> Self {
        NewError { val, }
    }

    pub fn into_inner(self) -> T {
        self.val
    }
}

// SAFETY: at most one thread gets a pointer to each chunk of data.
unsafe impl<T> Sync for Slab<T> { }

unsafe impl<T> GlobalAlloc for Slab<T> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        Slab::alloc(self, layout)
            .map(NonNull::as_ptr)
            .unwrap_or_else(null_mut)
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}
