//! The slab allocator.
//!
//! Basics of usage and the connection between the structs is discussed in the documentation of the
//! [`Slab`] itself.
//!
//! [`Slab`]: struct.Slab.html
use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;
use core::mem::{self, MaybeUninit};
use core::ptr::{NonNull, null_mut};
use core::sync::atomic::{AtomicUsize, Ordering};

use super::{Box, Uninit};
use crate::rc::Rc;

/// Allocator drawing from an inner, statically sized memory resource.
///
/// The type parameter `T` is used only to annotate the required size and alignment of the region
/// and has no futher use. Note that in particular there is no safe way to retrieve or unwrap an
/// inner instance even if the `Slab` was not constructed as a shared global static. Nevertheless,
/// the choice of type makes it easier to reason about potentially required extra space due to
/// alignment padding.
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
/// Take care, some runtime features of Rust will allocate some memory before or after your own
/// code. In particular, it was found to be be tricky to predict the usage of the builtin test
/// framework which seemingly allocates some structures per test.
///
/// ## Usage as a non-dropping local allocator
///
/// It is also possible to use a `Slab` as a stack local allocator or a specialized allocator. The
/// interface offers some utilities for allocating values from references to shared or unshared
/// instances directly. **Note**: this will never call the `Drop` implementation of the allocated
/// type. In particular, it would almost surely not be safe to `Pin` the values, except if there is
/// a guarantee for the `Slab` itself to not be deallocated either.
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
///     /// Avoid stack allocation of the full struct.
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
/// The ordering used is currently `SeqCst`. This enforces a single global sequence of observed
/// effects on the slab level. The author is fully aware that this is not strictly necessary. In
/// fact, even `AcqRel` may not be required as the monotonic bump allocator does not synchronize
/// other memory itself. If you bring forward a PR with a formalized reasoning for relaxing the
/// requirements to `Relaxed` (llvm `Monotonic`) it will be greatly appreciated (even more if you
/// demonstrate performance gains).
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

/// A value could not be moved into a slab allocation.
///
/// The error contains the value for which the allocation failed. Storing the value in the error
/// keeps it alive in all cases. This prevents the `Drop` implementation from running and preserves
/// resources which may otherwise not be trivial to restore.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LeakError<T> {
    val: T,
    failure: Failure,
}

/// Specifies an amount of consumed space of a slab.
///
/// Each allocation of the `Slab` increases the current level as they must not be empty. By
/// ensuring that an allocation is performed at a specific level it is thus possible to check that
/// multiple allocations happened in succession without other intermediate allocations. This
/// ability in turns makes it possible to group allocations together, for example to initialize a
/// `#[repr(C)]` struct member-by-member or to extend a slice.
///
/// ## Usage
///
/// The main use is successively allocating a slice without requiring all data to be present at
/// once. Other similar interface often require an internal locking mechanism but `Level` leaves
/// the choice to the user. This is not yet encapsulate in a safe API yet `Level` makes it easy to
/// reason about.
///
/// ```
/// # use core::slice;
/// # use static_alloc::slab::{Level, Slab};
/// static SLAB: Slab<[u64; 4]> = Slab::uninit();
///
/// /// Gathers as much data as possible.
/// ///
/// /// An arbitrary amount of data, can't stack allocate!
/// fn gather_data(mut iter: impl Iterator<Item=u64>) -> &'static mut [u64] {
///     let first = match iter.next() {
///         Some(item) => item,
///         None => return &mut [],
///     };
///
///     let mut level: Level = SLAB.level();
///     let mut begin: *mut u64;
///     let mut count;
///
///     match SLAB.leak_at(first, level) {
///         Ok((first, first_level)) => {
///             begin = first;
///             level = first_level;
///             count = 1;
///         },
///         _ => return &mut [],
///     }
///
///     let _ = iter.try_for_each(|value: u64| {
///         match SLAB.leak_at(value, level) {
///             Err(err) => return Err(err),
///             Ok((_, new_level)) => level = new_level,
///         };
///         count += 1;
///         Ok(())
///     });
///
///     unsafe {
///         // SAFETY: all `count` allocations are contiguous, begin is well aligned and no
///         // reference is currently pointing at any of the values. The lifetime is `'static` as
///         // the SLAB itself is static.
///         slice::from_raw_parts_mut(begin, count)
///     }
/// }
///
/// fn main() {
///     // There is no other thread running, so this succeeds.
///     let slice = gather_data(0..=3);
///     assert_eq!(slice, [0, 1, 2, 3]);
/// }
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Level(usize);

/// A successful allocation and current [`Level`].
///
/// [`Level`]: struct.Level.html
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Allocation {
    /// Pointer to the region with specified layout.
    pub ptr: NonNull<u8>,

    /// The observed amount of consumed bytes.
    pub level: Level,
}

/// Values of for some allocation including the [`Uninit`].
///
/// See [`Uninit`] for a better picture of the potential usage of this result.
///
/// [`Uninit`]: ../uninit/struct.Uninit.html
#[derive(Debug)]
pub struct UninitAllocation<'a, T=()> {
    /// Uninit pointer to the region with specified layout.
    pub uninit: Uninit<'a, T>,

    /// The observed amount of consumed bytes after the allocation.
    pub level: Level,
}

/// Reason for a failed allocation at an exact [`Level`].
///
/// [`Level`]: struct.Level.html
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Failure {
    /// No space left for that allocation.
    Exhausted,

    /// The allocation would not have used the expected base location.
    ///
    /// Reports the location that was observed. When only levels from the same slab are used (which
    /// should normally be the case) then the observed level is monotonically increasing.
    Mismatch {
        /// The observed level that was different from the requested one.
        observed: Level,
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
        Some(self.try_alloc(layout)?.uninit.as_non_null().cast())
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
        -> Result<Allocation, Failure>
    {
        let UninitAllocation { uninit, level } = self.try_alloc_at(layout, level.0)?;

        Ok(Allocation {
            ptr: uninit.as_non_null().cast(),
            level,
        })
    }

    /// Get an allocation with detailed layout.
    ///
    /// Provides an [`Uninit`] wrapping several aspects of initialization in a safe interface,
    /// bound by the lifetime of the reference to the allocator.
    ///
    /// [`Uninit`]: ../uninit/struct.Uninit.html
    pub fn get_layout(&self, layout: Layout)
        -> Option<UninitAllocation<'_>>
    {
        self.try_alloc(layout)
    }

    /// Get an allocation with detailed layout at a specific level.
    ///
    /// Provides an [`Uninit`] wrapping several aspects of initialization in a safe interface,
    /// bound by the lifetime of the reference to the allocator.
    ///
    /// Since the underlying allocation is the same, it would be `unsafe` but justified to fuse
    /// this allocation with the preceding or succeeding one.
    ///
    /// [`Uninit`]: ../uninit/struct.Uninit.html
    pub fn get_layout_at(&self, layout: Layout, at: Level)
        -> Result<UninitAllocation<'_>, Failure>
    {
        self.try_alloc_at(layout, at.0)
    }

    /// Get an allocation for a specific type.
    ///
    /// It is not yet initialized but provides a safe interface for that initialization.
    ///
    /// ## Usage
    ///
    /// ```
    /// # use static_alloc::Slab;
    /// use core::cell::{Ref, RefCell};
    ///
    /// let slab: Slab<[Ref<'static, usize>; 1]> = Slab::uninit();
    /// let data = RefCell::new(0xff);
    ///
    /// // We can place a `Ref` here but we did not yet.
    /// let alloc = slab.get::<Ref<usize>>().unwrap();
    /// let cell_ref = alloc.uninit.init(data.borrow());
    ///
    /// assert_eq!(**cell_ref, 0xff);
    /// ```
    pub fn get<V>(&self) -> Option<UninitAllocation<V>> {
        if mem::size_of::<V>() == 0 {
            return Some(self.zst_fake_alloc());
        }

        let layout = Layout::new::<V>();
        let UninitAllocation { uninit, level, } = self.try_alloc(layout)?;

        Some(UninitAllocation {
            // UNWRAP: it has exactly the requested size of `V`.
            uninit: uninit.cast().ok().unwrap(),
            level,
        })
    }

    /// Get an allocation for a specific type at a specific level.
    ///
    /// See [`get`] for usage.
    ///
    /// [`get`]: #method.get
    pub fn get_at<V>(&self, level: Level) -> Result<UninitAllocation<V>, Failure> {
        if mem::size_of::<V>() == 0 {
            let fake = self.zst_fake_alloc();
            // Note: zst_fake_alloc is a noop on the level, we may as well check after.
            if fake.level != level {
                return Err(Failure::Mismatch {
                    observed: fake.level,
                });
            }
            return Ok(fake);
        }

        let layout = Layout::new::<V>();
        let UninitAllocation { uninit, level, } = self.try_alloc_at(layout, level.0)?;

        Ok(UninitAllocation {
            // UNWRAP: it has exactly the requested size of `V`.
            uninit: uninit.cast().ok().unwrap(),
            level,
        })
    }

    pub fn boxed<V>(&self, val: V) -> Option<Box<'_, V>> {
        let alloc = self.get::<V>()?;
        Some(Box::new(val, alloc.uninit))
    }

    pub fn rc<V>(&self, val: V) -> Option<Rc<'_, V>> {
        let alloc = self.get_layout(Rc::<V>::layout())?;
        Some(Rc::new(val, alloc.uninit))
    }

    /// Observe the current level.
    ///
    /// Keep in mind that concurrent usage of the same slab may modify the level before you are
    /// able to use it in `alloc_at`. Calling this method provides also no other guarantees on
    /// synchronization of memory accesses, only that the values observed by the caller are a
    /// monotonically increasing seequence.
    pub fn level(&self) -> Level {
        Level(self.consumed.load(Ordering::SeqCst))
    }

    fn try_alloc(&self, layout: Layout)
        -> Option<UninitAllocation<'_>>
    {
        // Guess zero, this will fail when we try to access it and it isn't.
        let mut consumed = 0;
        loop {
            match self.try_alloc_at(layout, consumed) {
                Ok(alloc) => return Some(alloc),
                Err(Failure::Exhausted) => return None,
                Err(Failure::Mismatch{ observed }) => consumed = observed.0,
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
    fn try_alloc_at(&self, layout: Layout, expect_consumed: usize)
        -> Result<UninitAllocation<'_>, Failure>
    {
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

        let ptr = NonNull::new(aligned).unwrap();
        let uninit = unsafe {
            // SAFETY: memory is valid and unaliased for the lifetime of our reference.
            Uninit::from_memory(ptr.cast(), requested)
        };

        Ok(UninitAllocation {
            uninit,
            level: Level(new_consumed),
        })
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
    pub fn leak<V>(&self, val: V) -> Result<&mut V, LeakError<V>> {
        match self.get::<V>() {
            Some(alloc) => Ok(alloc.uninit.init(val)),
            None => Err(LeakError::new(val, Failure::Exhausted)),
        }
    }

    /// Allocate a value with a precise location.
    ///
    /// See [`leak`] for basics on allocation of values.
    ///
    /// The level is an identifer for a base location (more at [`level`]). This will succeed if it
    /// can be allocate exactly at the expected location.
    ///
    /// This method will return the new level of the slab allocator. A next allocation at the
    /// returned level will be placed next to this allocation, only separated by necessary padding
    /// from alignment. In particular, this is the same strategy as applied for the placement of
    /// `#[repr(C)]` struct members. (Except for the final padding at the last member to the full
    /// struct alignment.)
    ///
    /// ## Usage
    ///
    /// ```
    /// use static_alloc::Slab;
    ///
    /// let local: Slab<[u64; 3]> = Slab::uninit();
    ///
    /// let base = local.level();
    /// let (one, level) = local.leak_at(1_u64, base).unwrap();
    /// // Will panic when an allocation happens in between.
    /// let (two, _) = local.leak_at(2_u64, level).unwrap();
    ///
    /// assert_eq!((one as *const u64).wrapping_offset(1), two);
    /// ```
    ///
    /// [`leak`]: #method.leak
    /// [`level`]: #method.level
    pub fn leak_at<V>(&self, val: V, level: Level)
        -> Result<(&mut V, Level), LeakError<V>>
    {
        let alloc = match self.get_at::<V>(level) {
            Ok(alloc) => alloc,
            Err(err) => return Err(LeakError::new(val, err)),
        };

        let mutref = alloc.uninit.init(val);
        Ok((mutref, alloc.level))
    }

    /// 'Allocate' a ZST.
    fn zst_fake_alloc<Z>(&self) -> UninitAllocation<Z> {
        UninitAllocation {
            uninit: Uninit::invent_for_zst(),
            level: self.level(),
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

impl<T> LeakError<T> {
    fn new(val: T, failure: Failure) -> Self {
        LeakError { val, failure, }
    }

    /// Inspect the cause of this error.
    pub fn kind(&self) -> Failure {
        self.failure
    }

    /// Retrieve the value that could not be allocated.
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

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        // We are a slab allocator and do not deallocate.
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zst_no_drop() {
        #[derive(Debug)]
        struct PanicOnDrop;

        impl Drop for PanicOnDrop {
            fn drop(&mut self) {
                panic!("No instance of this should ever get dropped");
            }
        }

        let alloc = Slab::<()>::uninit();
        let _ = alloc.leak(PanicOnDrop).unwrap();
    }
}
