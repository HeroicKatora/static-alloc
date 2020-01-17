//! Reference counter value.
//!
//! See [`Rc`] for more information.
//!
//! [`Rc`]: ./struct.Rc.html
use core::{borrow, cmp, fmt, hash, mem, ops, ptr};
use core::alloc::Layout;
use core::cell::Cell;

use crate::uninit::{Uninit, UninitView};

/// A single-threaded reference-counting pointer. 'Rc' stands for 'Reference Counted'.
///
/// The inherent methods are all associated functions. This means you can not call them
/// unexpectedly through deref-coercion the reference itself. Instead, you need to call them as
/// `Rc::try_unwrap(rc)` etc. .
///
/// Compared to the standard library version, this will perform its own allocation. Instead, you
/// can ask [`Bump`] to perform them or manually allocate guided by the necessary [`layout`].
///
/// [`Bump`]: ../slab/struct.Bump.html#method.rc
/// [`layout`]: #method.layout
pub struct Rc<'a, T> {
    /// Shared view on the memory of the box.
    ///
    /// It is important **NOT** to safely expose this to the user. The weak counter maintains the
    /// invariant that the pointed-to memory is no longer aliased when the last Rc to that view has
    /// been dropped.
    inner: UninitView<'a, RcBox<T>>,
}

/// A reference-counting pointer to the allocation of an `Rc`.
///
/// ## TODO
///
/// Evaluate an interface:
/// ```ignore
/// fn reinit(&self, val: T) -> Result<Rc<T>, T>;
/// ```
pub struct Weak<'a, T> {
    /// Shared view on the memory of the box.
    ///
    /// The inner `val` of the box may have been de-initialized already. So we must be very careful
    /// to never create an actual reference to the box.
    inner: UninitView<'a, RcBox<T>>,
}

/// A structured container for the boxed value.
///
/// It's representation is chosen such that it can be cast to `Uninit<T>` and from it given
/// appropriate additional space. All added data is at the end of the allocation, this allows other
/// containers that store the value to reuse the same allocation without shoveling data around.
///
/// That however, is an implementation detail since we could also `memmove` appropriately. And it
/// falls apart as soon as we take extra alignment requirements into account. Hence, we do not
/// expose it generally and give no guarantees outside the basic conversion. Make this
/// incrementally better.
#[repr(C)]
struct RcBox<T> {
    /// Keep this member first!
    ///
    /// Note that `as_mut_ptr` and `into_raw` rely on this.
    val: T,

    /// The number of owners of the value.
    strong: Cell<usize>,

    /// The number of owners of the memory view.
    ///
    /// Note that the strong ownership of the value also counts as a *single* weak ownership. The
    /// last access which drops the value should also decrease the weak count.
    weak: Cell<usize>,
}

impl<'a, T> Rc<'a, T> {
    /// Constructs a new `Rc<T>`.
    ///
    /// See also [`Bump::rc`], which encapsulates the process of allocation and construction in a
    /// single method call.
    ///
    /// ## Panics
    /// This function panics if the memory is not valid for the layout of [`Rc::layout`].
    ///
    /// ## Examples
    ///
    /// ```
    /// use core::convert::TryInto;
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc};
    /// use static_alloc::Bump;
    ///
    /// struct Foo(u32);
    ///
    /// let slab: Bump<[u8; 1024]> = Bump::uninit();
    /// let layout = Rc::<Foo>::layout().try_into().unwrap();
    /// let memory = slab.alloc_layout(layout).unwrap();
    /// let rc = Rc::new(Foo(0), memory.uninit);
    /// ```
    ///
    /// [`Rc::layout`]: #method.layout
    /// [`Bump::rc`]: ../slab/struct.Bump.html#method.rc
    pub fn new(val: T, memory: Uninit<'a, ()>) -> Self {
        assert!(memory.fits(Self::layout()), "Provided memory must fit the inner layout");
        let mut memory = memory.cast::<RcBox<T>>().unwrap();

        memory.borrow_mut().init(RcBox {
            val,
            strong: Cell::new(1),
            weak: Cell::new(1),
        });

        Rc {
            inner: memory.into(),
        }
    }

    /// Wrap a raw initialized value back into an `Rc`.
    ///
    /// ## Safety
    /// The block must originate from a previous call to [`into_raw`] and only the value must have
    /// been modified. The value must still be valid.
    pub unsafe fn from_raw(init: Uninit<'a, T>) -> Self {
        debug_assert!(init.fits(Self::layout()), "Provided memory must fit the inner layout");
        let inner = init.cast().unwrap();

        Rc {
            inner: inner.into(),
        }
    }

    /// Try to extract the memory.
    ///
    /// This returns `Some` only when this is the last strong *and* weak reference to the value.
    /// The contained value will be preserved and is not dropped. Use `from_raw` to reinitialize a
    /// new `Rc` with the old value and memory.
    ///
    /// ## Example
    ///
    /// ```
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc};
    /// use static_alloc::Bump;
    ///
    /// struct HotPotato;
    ///
    /// impl Drop for HotPotato {
    ///     fn drop(&mut self) {
    ///         panic!("dropped!");
    ///     }
    /// }
    ///
    /// let slab: Bump<[u8; 1024]> = Bump::uninit();
    /// let foo = slab.rc(HotPotato).unwrap();
    ///
    /// let raw = Rc::into_raw(foo).ok().unwrap();
    /// // No panic. Value has not been dropped.
    /// ```
    pub fn into_raw(rc: Self) -> Result<Uninit<'a, T>, Self> {
        if !Rc::is_unique(&rc) {
            // Note: implicitely decrements `strong`
            return Err(rc);
        }

        let ptr = rc.inner.as_non_null();
        let len = rc.inner.size();
        mem::forget(rc);
        unsafe {
            // SAFETY: restored the memory we just forgot. We are the only reference to it, so it
            // is fine to restore the original unqiue allocation reference.
            Ok(Uninit::from_memory(ptr.cast(), len).cast().unwrap())
        }
    }

    /// Returns the contained value, if the `Rc` has exactly one strong reference.
    ///
    /// Also returns the managed memory in the form of a `Weak`. This is unusual but the best
    /// choice for potentially recovering it. Returning the memory directly is not possible since
    /// other `Weak<T>` instances may still point to it. If you are not interested in the memory
    /// you can simply drop the `Weak`.
    pub fn try_unwrap(rc: Self) -> Result<(T, Weak<'a, T>), Self> {
        if Rc::strong_count(&rc) != 1 {
            return Err(rc);
        }

        rc.dec_strong();
        let val = unsafe { ptr::read(rc.as_ptr()) };

        let weak = Weak { inner: rc.inner };
        mem::forget(rc);

        Ok((val, weak))
    }

    /// Create a new `Weak` pointer to the value.
    ///
    /// The weak pointer shares ownership over the memory but not over the value itself.
    ///
    /// ## Example
    ///
    /// ```
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc};
    /// use static_alloc::Bump;
    ///
    /// struct Foo;
    ///
    /// let slab: Bump<[u8; 1024]> = Bump::uninit();
    /// let foo = slab.rc(Foo).unwrap();
    /// let weak = Rc::downgrade(&foo);
    ///
    /// assert_eq!(Rc::weak_count(&foo), 2);
    /// drop(foo);
    ///
    /// assert_eq!(weak.weak_count(), 1);
    /// ```
    pub fn downgrade(rc: &Self) -> Weak<'a, T> {
        rc.inc_weak();
        Weak { inner: rc.inner }
    }
}

impl<T> Rc<'_, T> {
    /// Get the layout for memory passed to [`Rc::new`].
    ///
    /// You should not rely on the value returned here. The two guarantees are: the size of the
    /// layout is at least as large as the input type and it is never empty.
    ///
    /// An `Rc` does not simply point to a lone instance of a type but instead adds some small
    /// metadata (two pointer-sized counters). To keep the implementation details private, this
    /// method allows allocation of properly sized regions without exposing the exact type that
    /// will be stored on the heap.
    ///
    /// ## Examples
    ///
    /// ```
    /// use without_alloc::rc::Rc;
    ///
    /// struct Foo(u32);
    /// struct Empty;
    ///
    /// assert!(Rc::<Foo>::layout().size() >= 4);
    /// assert!(Rc::<Empty>::layout().size() > 0);
    /// ```
    ///
    /// [`Rc::new`]: #method.new
    pub fn layout() -> Layout {
        // FIXME: this should really be `const` but `Layout` does not offer that yet.
        Layout::new::<RcBox<T>>()
    }

    /// Gets the number of weak pointers to the value.
    ///
    /// Note that all `Rc` to the same value count as one weak pointer in total.
    pub fn weak_count(rc: &Self) -> usize {
        rc.inner().weak.get()
    }

    /// Gets the number of strong pointers to the value.
    pub fn strong_count(rc: &Self) -> usize {
        rc.inner().strong.get()
    }

    /// Try to retrieve a mutable reference to the value.
    ///
    /// This method will only succeed if there are no other pointers to the same value, neither
    /// strong ones nor weak ones.
    pub fn get_mut(rc: &mut Self) -> Option<&mut T> {
        if rc.is_unique() {
            Some(unsafe { &mut *rc.as_mut_ptr() })
        } else {
            None
        }
    }

    /// Check if two `Rc`s point to the same data.
    ///
    /// This will never compare the values but simply inspect the inner pointers.
    ///
    /// ## Example
    ///
    /// ```
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc};
    /// use static_alloc::Bump;
    ///
    /// struct Foo;
    ///
    /// let slab: Bump<[u8; 1024]> = Bump::uninit();
    ///
    /// // Two Rc's pointing to the same data.
    /// let foo = slab.rc(Foo).unwrap();
    /// let foo2 = Rc::clone(&foo);
    ///
    /// // An unrelated allocation.
    /// let not_foo = slab.rc(Foo).unwrap();
    ///
    /// assert!( Rc::ptr_eq(&foo, &foo2));
    /// assert!(!Rc::ptr_eq(&foo, &not_foo));
    /// ```
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.inner.as_ptr() == other.inner.as_ptr()
    }

    /// Get a reference to the inner box.
    ///
    /// Note that we must not mutably touch or reference the inner `T` through the reference by
    /// casting to mutable pointers.
    fn inner(&self) -> &RcBox<T> {
        unsafe {
            self.inner.as_ref()
        }
    }

    fn is_unique(&self) -> bool {
        Rc::strong_count(self) == 1 && Rc::weak_count(self) == 1
    }

    /// Get the mutable pointer to the value.
    ///
    /// This relies on the layout of the inner struct.
    fn as_mut_ptr(&mut self) -> *mut T {
        // `T` is the first member, #[repr(C)] makes this cast well behaved.
        self.inner.as_ptr() as *mut T
    }

    /// Get the pointer to the value.
    ///
    /// This relies on the layout of the inner struct.
    fn as_ptr(&self) -> *const T {
        self.inner.as_ptr() as *const T
    }

    fn inc_strong(&self) {
        let val = Self::strong_count(self) + 1;
        self.inner().strong.set(val);
    }

    fn dec_strong(&self) {
        let val = Self::strong_count(self) - 1;
        self.inner().strong.set(val);
    }

    fn inc_weak(&self) {
        let val = Self::weak_count(self) + 1;
        self.inner().weak.set(val);
    }

    fn dec_weak(&self) {
        let val = Self::weak_count(self) - 1;
        self.inner().weak.set(val);
    }
}

impl<'a, T> Weak<'a, T> {
    /// Try to unwrap the original allocation of the `Rc`.
    ///
    /// This will only work when this is the only pointer to the allocation. That is, there are
    /// neither `Weak` nor `Rc` still pointing at it.
    ///
    /// ## Example
    ///
    /// ```
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc};
    /// use static_alloc::Bump;
    ///
    /// struct Foo;
    ///
    /// let slab: Bump<[u8; 1024]> = Bump::uninit();
    /// let rc = slab.rc(Foo).unwrap();
    /// let (_, weak) = Rc::try_unwrap(rc).ok().unwrap();
    ///
    /// // This is the only one pointing at the allocation.
    /// let memory = weak.try_unwrap().ok().unwrap();
    /// ```
    pub fn try_unwrap(self) -> Result<Uninit<'a, ()>, Self> {
        if !self.is_unique_to_rc_memory() {
            return Err(self);
        }

        let ptr = self.inner.as_non_null();
        let len = self.inner.size();
        unsafe {
            // SAFETY: restored the memory that an rc has originally provided to the `Weak`. We are
            // the only reference to it, so it is fine to restore the original unqiue allocation
            // reference.
            Ok(Uninit::from_memory(ptr.cast(), len))
        }
    }

    /// Attempt to upgrade to a shared pointer to the value.
    ///
    /// This operation will only succeed if there are still strong pointers to the value, i.e.
    /// `strong_count` is not zero. Then the value has not been dropped yet and its lifetime is
    /// extended.
    ///
    /// ```
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc};
    /// use static_alloc::Bump;
    ///
    /// let memory: Bump<[u8; 1024]> = Bump::uninit();
    /// let rc = memory.rc(0usize).unwrap();
    ///
    /// let weak = Rc::downgrade(&rc);
    /// let rc2 = weak.upgrade().unwrap();
    ///
    /// drop(rc);
    /// drop(rc2);
    ///
    /// // No more strong pointers left.
    /// assert!(weak.upgrade().is_none());
    /// ```
    pub fn upgrade(&self) -> Option<Rc<'a, T>> {
        if self.strong_count() == 0 {
            None
        } else { 
            let rc = Rc { inner: self.inner };
            rc.inc_strong();
            Some(rc)
        }
    }
}

impl<T> Weak<'_, T> {
    /// Gets the number of strong pointers pointing at the value.
    ///
    /// ## Example
    ///
    /// ```
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc, rc::Weak};
    /// use static_alloc::Bump;
    ///
    /// struct Foo;
    ///
    /// let slab: Bump<[u8; 1024]> = Bump::uninit();
    /// let rc = slab.rc(Foo).unwrap();
    /// let (_, weak) = Rc::try_unwrap(rc).ok().unwrap();
    ///
    /// // We just destroyed the only one.
    /// assert_eq!(Weak::strong_count(&weak), 0);
    /// ```
    pub fn strong_count(&self) -> usize {
        self.strong().get()
    }

    /// Gets the number of weak pointers pointing at the value.
    ///
    /// ## Example
    ///
    /// ```
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc, rc::Weak};
    /// use static_alloc::Bump;
    ///
    /// struct Foo;
    ///
    /// let slab: Bump<[u8; 1024]> = Bump::uninit();
    /// let rc = slab.rc(Foo).unwrap();
    /// let (_, weak) = Rc::try_unwrap(rc).ok().unwrap();
    ///
    /// // This is the only one pointing at the allocation.
    /// assert_eq!(Weak::weak_count(&weak), 1);
    /// ```
    pub fn weak_count(&self) -> usize {
        self.weak().get()
    }

    fn is_unique_to_rc_memory(&self) -> bool {
        self.strong_count() == 0 && self.weak_count() == 1
    }

    /// Get a reference to the weak counter.
    ///
    /// Avoids potential UB, never creates a reference to the potentially dead `val`.
    fn weak(&self) -> &Cell<usize> {
        unsafe { &(*self.inner.as_ptr()).weak }
    }

    /// Get a reference to the strong counter.
    ///
    /// Avoids potential UB, never creates a reference to the potentially dead `val`.
    fn strong(&self) -> &Cell<usize> {
        unsafe { &(*self.inner.as_ptr()).strong }
    }

    fn inc_weak(&self) {
        let val = Weak::weak_count(self);
        self.weak().set(val + 1);
    }

    fn dec_weak(&self) {
        let val = Weak::weak_count(self);
        self.weak().set(val - 1);
    }
}

impl<T> Drop for Rc<'_, T> {
    /// Drops the `Rc`.
    ///
    /// This will decrement the strong reference count. If the strong reference
    /// count reaches zero then the only other references (if any) are
    /// [`Weak`], so we `drop` the inner value.
    ///
    /// # Examples
    ///
    /// ```
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc};
    /// use static_alloc::Bump;
    ///
    /// struct Foo;
    ///
    /// impl Drop for Foo {
    ///     fn drop(&mut self) {
    ///         println!("dropped!");
    ///     }
    /// }
    ///
    /// let slab: Bump<[u8; 1024]> = Bump::uninit();
    ///
    /// let foo  = slab.rc(Foo).unwrap();
    /// let foo2 = Rc::clone(&foo);
    ///
    /// drop(foo);    // Doesn't print anything
    /// drop(foo2);   // Prints "dropped!"
    /// ```
    fn drop(&mut self) {
        self.dec_strong();
        // weak count doesn't actually do anything.
        if Rc::strong_count(self) == 0 {
            self.dec_weak();

            unsafe {
                ptr::drop_in_place(self.as_mut_ptr())
            }
        }
    }
}

impl<T> ops::Deref for Rc<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.inner().val
    }
}

impl<T> Clone for Rc<'_, T> {
    /// Clone the `Rc`.
    ///
    /// This will increment the strong reference count. Only an Rc pointing to a unique value can
    /// unwrap or point to the value mutably.
    ///
    /// # Examples
    ///
    /// ```
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc};
    /// use static_alloc::Bump; 
    ///
    /// struct Foo;
    ///
    /// let slab: Bump<[u8; 1024]> = Bump::uninit();
    ///
    /// let mut foo  = slab.rc(Foo).unwrap();
    /// assert!(Rc::get_mut(&mut foo).is_some());
    ///
    /// let foo2 = Rc::clone(&foo);
    /// assert!(Rc::get_mut(&mut foo).is_none());
    /// ```
    fn clone(&self) -> Self {
        self.inc_strong();
        Rc {
            inner: self.inner,
        }
    }
}

impl<T> Drop for Weak<'_, T> {
    fn drop(&mut self) {
        self.dec_weak();
        // It doesn't matter what happens to the memory.
    }
}

impl<T> Clone for Weak<'_, T> {
    /// Clone the `Weak`.
    ///
    /// This will increment the weak reference count.
    ///
    /// # Examples
    ///
    /// ```
    /// use without_alloc::{alloc::LocalAllocLeakExt, rc::Rc};
    /// use static_alloc::Bump;
    ///
    /// struct Foo;
    ///
    /// let slab: Bump<[u8; 1024]> = Bump::uninit();
    /// let foo = slab.rc(Foo).unwrap();
    ///
    /// let (_, weak) = Rc::try_unwrap(foo).ok().unwrap();
    /// assert_eq!(weak.weak_count(), 1);
    ///
    /// let weak2 = weak.clone();
    /// assert_eq!(weak.weak_count(), 2);
    /// assert_eq!(weak2.weak_count(), 2);
    /// ```
    fn clone(&self) -> Self {
        self.inc_weak();
        Weak {
            inner: self.inner,
        }
    }
}

impl<'a, 'b, T: PartialEq> PartialEq<Rc<'b, T>> for Rc<'a, T> {
    #[inline]
    fn eq(&self, other: &Rc<T>) -> bool {
        PartialEq::eq(&**self, &**other)
    }
    #[inline]
    fn ne(&self, other: &Rc<T>) -> bool {
        PartialEq::ne(&**self, &**other)
    }
}

impl<T: Eq> Eq for Rc<'_, T> { }

impl<'a, 'b, T: PartialOrd> PartialOrd<Rc<'b, T>> for Rc<'a, T> {
    #[inline]
    fn partial_cmp(&self, other: &Rc<T>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
    #[inline]
    fn lt(&self, other: &Rc<T>) -> bool {
        PartialOrd::lt(&**self, &**other)
    }
    #[inline]
    fn le(&self, other: &Rc<T>) -> bool {
        PartialOrd::le(&**self, &**other)
    }
    #[inline]
    fn ge(&self, other: &Rc<T>) -> bool {
        PartialOrd::ge(&**self, &**other)
    }
    #[inline]
    fn gt(&self, other: &Rc<T>) -> bool {
        PartialOrd::gt(&**self, &**other)
    }
}

impl<T: Ord> Ord for Rc<'_, T> {
    #[inline]
    fn cmp(&self, other: &Rc<T>) -> cmp::Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<T: hash::Hash> hash::Hash for Rc<'_, T> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

impl<T: fmt::Display> fmt::Display for Rc<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: fmt::Debug> fmt::Debug for Rc<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T> fmt::Pointer for Rc<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<T> borrow::Borrow<T> for Rc<'_, T> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T> AsRef<T> for Rc<'_, T> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

#[cfg(test)]
mod tests {
    use core::alloc::Layout;
    use core::cell::Cell;

    use super::{RcBox, Rc, Weak};
    use static_alloc::Bump;
    use crate::alloc::LocalAllocLeakExt;

    #[test]
    fn layout_box_compatible() {
        let mut boxed = RcBox {
            val: 0usize,
            strong: Cell::new(1),
            weak: Cell::new(1),
        };

        let val_ptr = &boxed as *const _ as *const usize;
        assert_eq!(unsafe { *val_ptr }, 0);

        boxed.val = 0xdeadbeef;
        assert_eq!(unsafe { *val_ptr }, 0xdeadbeef);
    }

    #[test]
    fn control_through_counters() {
        struct Duck;
        struct NeverDrop;

        impl Drop for NeverDrop {
            fn drop(&mut self) {
                panic!("dropped!");
            }
        }

        let slab: Bump<[u8; 1024]> = Bump::uninit();
        let rc = slab.rc(NeverDrop).unwrap();
        rc.inc_strong();
        drop(rc);

        let mut rc = slab.rc(Duck).unwrap();
        assert_eq!(rc.as_mut_ptr() as *const u8, rc.inner.as_ptr() as *const u8);
        assert_eq!(rc.as_ptr() as *const u8, rc.inner.as_ptr() as *const u8);

        let rc = slab.rc(Duck).unwrap();
        // Forbidden in public, but we do not grab mutable references.
        let inner = rc.inner;
        drop(rc);
        unsafe {
            assert_eq!((*inner.as_ptr()).strong.get(), 0);
            assert_eq!((*inner.as_ptr()).weak.get(), 0);
        }

        let rc = slab.rc(Duck).unwrap();
        let (_, weak) = Rc::try_unwrap(rc).ok().unwrap();
        assert_eq!(Weak::strong_count(&weak), 0);
        assert_eq!(Weak::weak_count(&weak), 1);
        let inner = weak.inner;
        drop(weak);
        unsafe {
            assert_eq!((*inner.as_ptr()).strong.get(), 0);
            assert_eq!((*inner.as_ptr()).weak.get(), 0);
        }
    }

    #[test]
    #[should_panic = "inner layout"]
    fn wrong_layout_panics() {
        use core::convert::TryInto;

        struct Foo(u32);

        let slab: Bump<[u8; 1024]> = Bump::uninit();
        let layout = Layout::new::<Foo>().try_into().unwrap();
        let wrong_alloc = slab.alloc_layout(layout).unwrap();

        let _ = Rc::new(Foo(0), wrong_alloc.uninit);
    }
}
