use core::{
    ptr::{self, NonNull},
    marker::PhantomData,
    ops::{Deref, DerefMut}
};

/// Represents an allocation within a Node.
/// This is an owning pointer.
pub struct Allocation<'ctx, T> {
    // Covariance should be OK.
    pointer: NonNull<T>,
    lifetime: PhantomData<&'ctx T>,
}

impl <'ctx, T> Allocation<'ctx, T> {
    pub(crate) fn new(pointer: *mut T) -> Self {
        Self {
            pointer: NonNull::new(pointer).expect("Got a null pointer"),
            lifetime: PhantomData,
        }
    }
}

impl <'ctx, T> Deref for Allocation<'ctx, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.pointer.as_ref() }
    }
}


impl <'ctx, T> DerefMut for Allocation<'ctx, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.pointer.as_mut() }
    }
}

impl <T> Drop for Allocation<'_, T> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.pointer.as_ptr())
        }
    }
}