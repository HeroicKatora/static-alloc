//! This module contains an [`Allocation`]
//! struct.
use alloc_traits::AllocTime;

use core::{
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
};

/// Represents an allocation within a Bump.
/// This is an owning pointer.
#[allow(unused)]
pub struct Allocation<'ctx, T> {
    // Covariance should be OK.
    pointer: NonNull<T>,
    lifetime: AllocTime<'ctx>,
}

impl<'ctx, T> Allocation<'ctx, T> {
    pub(crate) fn new(pointer: *mut T) -> Self {
        Self {
            pointer: NonNull::new(pointer).expect("Got a null pointer"),
            lifetime: AllocTime::default(),
        }
    }
}

impl<'ctx, T> Deref for Allocation<'ctx, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.pointer.as_ref() }
    }
}

impl<'ctx, T> DerefMut for Allocation<'ctx, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.pointer.as_mut() }
    }
}

impl<T> Drop for Allocation<'_, T> {
    fn drop(&mut self) {
        unsafe { ptr::drop_in_place(self.pointer.as_ptr()) }
    }
}
