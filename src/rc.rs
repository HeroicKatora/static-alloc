//! Reference counter value.
//!
//!
use core::mem;
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
    strong: Cell<usize>,
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
        rc.inner().weak.get()
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

    fn inner(&self) -> &RcBox<T> {
        unsafe {
            self.inner.as_ref()
        }
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
    fn drop(&mut self) {
        unimplemented!()
    }
}

impl<T> Clone for Rc<'_, T> {
    fn clone(&self) -> Self {
        unimplemented!()
    }
}
