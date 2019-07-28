//! Reference counter value.
//!
//!
use core::{mem, ptr};
use core::alloc::Layout;
use core::cell::Cell;

use crate::uninit::{Uninit, UninitView};

pub struct Rc<'a, T> {
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

    pub unsafe fn from_raw(init: Uninit<'a, T>) -> Self {
        // TODO: offset from the val field.
        unimplemented!()
    }

    pub fn into_raw(rc: Self) -> Uninit<'a, T> {
        // TODO: offset to the val field.
        unimplemented!()
    }

    pub fn try_unwrap(b: Self) -> Result<(T, Uninit<'a, T>), Self> {
        unimplemented!()
    }
}

impl<T> Rc<'_, T> {
    pub fn layout() -> Layout {
        Layout::new::<RcBox<T>>()
    }

    pub fn weak_count(rc: &Self) -> usize {
        unimplemented!()
    }

    pub fn strong_count(rc: &Self) -> usize {
        rc.inner().strong.get()
    }

    pub fn get_mut(rc: &mut Self) -> Option<&mut T> {
        unimplemented!()
    }

    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        unimplemented!()
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

    fn as_mut_ptr(&mut self) -> *mut T {
        self.inner.as_ptr() as *mut T
    }

    fn inc_strong(&self) {
        let val = Self::strong_count(self) + 1;
        self.inner().strong.set(val);
    }

    fn dec_strong(&self) {
        let val = Self::strong_count(self) - 1;
        self.inner().strong.set(val);
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
    /// use static_alloc::{Slab, rc::Rc};
    ///
    /// struct Foo;
    ///
    /// impl Drop for Foo {
    ///     fn drop(&mut self) {
    ///         println!("dropped!");
    ///     }
    /// }
    ///
    /// let slab: Slab<[u8; 1024]> = Slab::uninit();
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
            unsafe {
                ptr::drop_in_place(self.as_mut_ptr())
            }
        }
    }
}

impl<T> Clone for Rc<'_, T> {
    fn clone(&self) -> Self {
        self.inc_strong();
        Rc {
            inner: self.inner,
        }
    }
}
