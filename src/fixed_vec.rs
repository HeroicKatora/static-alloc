//! Contains the `FixedVec` implementation.
//!
//! [See `FixedVec` for the main information][`FixedVec`].
//!
//! [`FixedVec`]: struct.FixedVec.html
use core::{ops, ptr, slice};
use crate::uninit::Uninit;

/// A `Vec`-like structure that does not manage its allocation.
///
/// This vector type will never (re-)allocate but it can also not free underused memory. As opposed
/// to other similar crates, it does require and additional bounds on its type parameter as it
/// truly manages uninitialized memory to store instances.
///
/// # Basic Usage
///
/// # Advanaced Usage
///
/// One focus of the library is composability. It should not be surprising that `FixedVec`
/// interacts with the [`Slab`] allocator, which implements a specialized interface providing the
/// [`Uninit`] type instead of a raw `*const u8`. Hence, the `FixedVec` can use this instead of its
/// own local stack variables.
///
/// ```
/// # use static_alloc::{FixedVec, Slab};
/// # use core::alloc::Layout;
/// let alloc: Slab<[u8; 1 << 12]> = Slab::uninit();
/// let some_usize = alloc.leak(0_usize).unwrap();
///
/// let mut vec: FixedVec<&usize> = FixedVec::from_available(
///     alloc.get_layout(Layout::new::<[&usize; 1]>()).unwrap().uninit);
/// // Push the reference to the other allocation.
/// vec.push(some_usize);
///
/// // … do something else
///
/// // Ensure lifetimes work out.
/// drop(vec);
/// ```
///
/// [`Slab`]: ../slab/struct.Slab.html
/// [`Uninit`]: ../uninit/struct.Uninit.html
pub struct FixedVec<'a, T> {
    uninit: Uninit<'a, [T]>,
    length: usize,
}

impl<T> FixedVec<'_, T> {
    /// Shorten the vector to a maximum length.
    ///
    /// If the length is not larger than `len` this has no effect.
    ///
    /// The tail of the vector is dropped starting from the last element. This is opposite to
    /// ([WIP] interface does not yet exist) `.drain(len..).for_each(drop)`.
    ///
    /// ## Example
    ///
    /// ```
    /// # use core::mem::MaybeUninit;
    /// # use static_alloc::{FixedVec, Uninit};
    ///
    /// let mut memory: MaybeUninit<[usize; 4]> = MaybeUninit::uninit();
    /// let uninit = Uninit::from(&mut memory).cast_slice().unwrap();
    /// let mut vec = FixedVec::new(uninit);
    ///
    /// vec.push(0usize);
    /// vec.push(1usize);
    /// vec.push(2usize);
    ///
    /// assert_eq!(vec.as_slice(), [0, 1, 2]);
    /// vec.truncate(1);
    /// assert_eq!(vec.as_slice(), [0]);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        struct SetLenOnDrop<'a> {
            len: &'a mut usize,
            local_len: usize,
        }

        impl Drop for SetLenOnDrop<'_> {
            fn drop(&mut self) {
                *self.len = self.local_len;
            }
        }

        let mut ptr = self.end_mut_ptr();
        let current_length = self.length;
        let mut set_len = SetLenOnDrop { len: &mut self.length, local_len: current_length };

        for _ in len..current_length {
            set_len.local_len -= 1;

            unsafe {
                ptr = ptr.offset(-1);
                ptr::drop_in_place(ptr);
            }
        }
    }

    /// Extracts a slice containing the entire vector.
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            // SAFETY: length is the number of initialized elements.
            slice::from_raw_parts(self.uninit.as_begin_ptr(), self.length)
        }
    }

    /// Extracts the mutable slice containing the entire vector.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            // SAFETY:
            // * length is the number of initialized elements.
            // * unaliased since we take ourselves by `mut` and `uninit` does the rest.
            slice::from_raw_parts_mut(self.uninit.as_begin_ptr(), self.length)
        }
    }

    /// Returns the number of elements in the vector.
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns the number of elements the vector can hold.
    pub fn capacity(&self) -> usize {
        self.uninit.capacity()
    }

    /// Returns `true` if the vector contains no elements.
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Appends an element to the back of a collection.
    ///
    /// Return `Err(val)` if it is not possible to append the element.
    ///
    /// ```
    /// use static_alloc::{FixedVec, Uninit};
    /// use core::mem::MaybeUninit;
    ///
    /// // Only enough storage for one element.
    /// let mut allocation: MaybeUninit<[u32; 1]> = MaybeUninit::uninit();
    /// let uninit = Uninit::from_maybe_uninit(&mut allocation);
    /// let mut vec = FixedVec::from_available(uninit);
    ///
    /// // First push succeeds.
    /// assert_eq!(vec.push(1), Ok(()));
    ///
    /// // The second push fails.
    /// assert_eq!(vec.push(2), Err(2));
    ///
    /// ```
    pub fn push(&mut self, val: T) -> Result<(), T> {
        if self.length == usize::max_value() {
            return Err(val);
        }

        let init = match self.head_tail_mut().1.split_first() {
            Some(init) => init,
            None => return Err(val),
        };

        init.init(val);
        self.length += 1;

        Ok(())
    }

    /// Removes the last element from a vector and returns it, or `None` if it is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.length == 0 {
            return None;
        }

        let last = self.head_tail_mut().0.split_last().unwrap();
        let val = unsafe {
            // SAFETY: initialized and no reference of any kind exists to it.
            ptr::read(last.as_ptr())
        };
        self.length -= 1;
        Some(val)
    }

    /// Split the capacity of the collection into two at a given index.
    ///
    /// In contrast to `Vec::split_off` calling this method reduces the capacity of `self` to `at`.
    ///
    /// ## Panics
    /// This method panics if `at > self.capacity()`.
    pub fn split_and_shrink_to(&mut self, at: usize) -> Self {
        assert!(at <= self.capacity(), "`at` out of bounds");
        // `self.length` is always smaller than `split_at`.
        let new_uninit = self.uninit.split_at(at).unwrap();
        // The first `at` elements stay in this vec.
        let new_len = self.length.saturating_sub(at);
        self.length = self.length - new_len;
        FixedVec {
            uninit: new_uninit,
            length: new_len,
        }
    }

    fn head_tail_mut(&mut self) -> (Uninit<'_, [T]>, Uninit<'_, [T]>) {
        // Borrow, do not affect the actual allocation by throwing away possible elements.
        let mut all = self.uninit.borrow_mut();
        // This must always be possible. `self.length` is nevery greater than the capacity.
        let tail = all.split_at(self.length).unwrap();
        (all, tail)
    }

    fn end_mut_ptr(&mut self) -> *mut T {
        unsafe { self.as_mut_ptr().add(self.length) }
    }
}

impl<'a, T> FixedVec<'a, T> {
    /// Create a `FixedVec` in a pre-allocated region.
    ///
    /// The capacity will be that of the underlying allocation.
    pub fn new(uninit: Uninit<'a, [T]>) -> Self {
        FixedVec {
            uninit,
            length: 0,
        }
    }

    /// Create a `FixedVec` with as large of a capacity as available.
    ///
    /// When no aligned slice can be create within the provided memory then the constructor will
    /// fallback to an empty dangling slice.
    ///
    /// This is only a utility function.
    pub fn from_available<U>(generic: Uninit<'a, U>) -> Self {
        let mut uninit = generic.as_memory();
        let slice = uninit.split_slice().unwrap_or_else(Uninit::empty);
        Self::new(slice)
    }

    /// Return trailing bytes that can not be used by the `FixedVec`.
    ///
    /// This operation is idempotent.
    pub fn shrink_to_fit(&mut self) -> Uninit<'a, ()> {
        self.uninit.shrink_to_fit()
    }
}

impl<T> ops::Deref for FixedVec<'_, T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> ops::DerefMut for FixedVec<'_, T> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T> Drop for FixedVec<'_, T> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.as_mut_slice())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::FixedVec;
    use crate::Uninit;

    use core::mem::MaybeUninit;
    use core::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn init_and_use() {
        #[derive(Debug, PartialEq, Eq)]
        struct Foo(usize);

        const CAPACITY: usize = 30;

        let mut allocation: MaybeUninit<[Foo; CAPACITY]> = MaybeUninit::uninit();
        let mut vec = FixedVec::from_available((&mut allocation).into());

        assert_eq!(vec.capacity(), CAPACITY);
        assert_eq!(vec.len(), 0);
        for i in 0..CAPACITY {
            assert_eq!(vec.push(Foo(i)), Ok(()));
        }

        assert_eq!(vec.capacity(), CAPACITY);
        assert_eq!(vec.len(), CAPACITY);

        for i in (0..CAPACITY).rev() {
            assert_eq!(vec.pop(), Some(Foo(i)));
        }

        assert_eq!(vec.capacity(), CAPACITY);
        assert_eq!(vec.len(), 0);
    }

    #[test]
    fn zst_drop() {
        const COUNT: usize = 30;
        static DROP_COUNTER: AtomicUsize = AtomicUsize::new(0);
        struct HasDrop(usize);

        impl Drop for HasDrop {
            fn drop(&mut self) {
                DROP_COUNTER.fetch_add(1, Ordering::SeqCst);
            }
        }


        let mut allocation: MaybeUninit<[HasDrop; COUNT]> = MaybeUninit::uninit();
        let mut vec = FixedVec::from_available((&mut allocation).into());

        for i in 0..COUNT {
            assert!(vec.push(HasDrop(i)).is_ok());
        }

        drop(vec);
        assert_eq!(DROP_COUNTER.load(Ordering::SeqCst), COUNT);
    }

    #[test]
    fn zst() {
        struct Zst;
        let vec = FixedVec::<Zst>::new(Uninit::empty());
        assert_eq!(vec.capacity(), usize::max_value());
    }

    #[test]
    fn split_and_shrink() {
        // Zeroed because we want to test the contents.
        let mut allocation: MaybeUninit<[u16; 8]> = MaybeUninit::zeroed();

        let mut aligned = Uninit::from(&mut allocation).as_memory();
        let _ = aligned.split_at_byte(15);

        let mut vec = FixedVec::from_available(aligned);
        let mut second = vec.split_and_shrink_to(4);
        let tail = second.shrink_to_fit();

        assert_eq!(vec.capacity(), 4);
        assert_eq!(vec.shrink_to_fit().size(), 0);
        assert_eq!(second.capacity(), 3);
        assert_eq!(second.shrink_to_fit().size(), 0);
        assert_eq!(tail.size(), 1);

        let _ = tail.cast::<u8>().unwrap().init(0xFF);
        (0_u16..4).for_each(|v| assert!(vec.push(v).is_ok()));
        (4..7).for_each(|v| assert!(second.push(v).is_ok()));

        assert_eq!(vec.len(), 4);
        assert_eq!(second.len(), 3);

        drop(vec);
        drop(second);
        assert_eq!(
            &unsafe { *allocation.as_ptr() }[..7],
            [0, 1, 2, 3, 4, 5, 6]);
    }

    /// Tests panics during truncation behave as expected.
    ///
    /// Unwinding started in a panic during truncation should not effect `Drop` calls when the
    /// `Vec` itself is hit by the unwinding. We test this by voluntarily triggering an unwinding
    /// and counting the number of values which have been dropped regularly (that is, during the
    /// `Drop` of `Vec` when it is unwound).
    ///
    /// Note that this test is already `should_panic` and the observable failure is thus an abort
    /// from a double panic!
    #[test]
    #[should_panic = "Trigger triggered"]
    fn drop_safe_in_truncation() {
        use core::cell::Cell;

        #[derive(Debug)]
        struct Trigger<'a> {
            panic_on_drop: bool,
            dropped_counter: &'a Cell<usize>,
        }

        impl Drop for Trigger<'_> {
            fn drop(&mut self) {
                if self.panic_on_drop { panic!("Trigger triggered") }
                // Record this as a normal drop.
                self.dropped_counter.set(self.dropped_counter.get() + 1);
            }
        }

        struct AbortMismatchedDropCount<'a> {
            counter: &'a Cell<usize>,
            expected: usize,
        }

        impl Drop for AbortMismatchedDropCount<'_> {
            fn drop(&mut self) {
                struct ForceDupPanic;

                impl Drop for ForceDupPanic {
                    fn drop(&mut self) { panic!() }
                }

                if self.expected != self.counter.get() {
                    // For duplicate panic, and thus abort
                    let _x = ForceDupPanic;
                    panic!();
                }
            }
        }

        let mut allocation: MaybeUninit<[u8; 512]> = MaybeUninit::zeroed();
        let drops = Cell::new(0);

        // Is `Drop`ed *after* the Vec, and will record the number of usually dropped Triggers.
        let _abort_mismatch_raii = AbortMismatchedDropCount {
            counter: &drops,
            expected: 1,
        };

        let uninit = Uninit::from(&mut allocation).as_memory();
        let mut vec = FixedVec::from_available(uninit);

        vec.push(Trigger { panic_on_drop: false, dropped_counter: &drops }).unwrap();
        vec.push(Trigger { panic_on_drop: true, dropped_counter: &drops }).unwrap();

        // Trigger!
        vec.truncate(1);
    }
}
