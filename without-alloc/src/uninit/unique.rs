use core::{alloc::Layout, mem, ptr::NonNull};
use alloc_traits::AllocTime;

use crate::uninit::ptr_layout::PtrLayout;

/// A variant of `NonNull` with a lifetime attached.
///
/// The lifetime has no special semantic interpretation but is not implicitly coercible to a
/// different one, even to a relaxed version.
#[repr(transparent)]
pub(crate) struct Local<'lt, T: ?Sized> {
    inner: NonNull<T>,
    time: AllocTime<'lt>,
}

/// A pointer to memory that is owned with exactly the layout of `T`.
///
/// The pointer must be unique for the lifetime `'lt`. It must also have provenance that allows it
/// to access the entire layout of `T`.
///
/// This is different from a mutable out pointer in that it is variant in the type parameter. This
/// is because we know, or rather unsafely require, that nothing else expects a valid `T` to live
/// at the pointee.
#[repr(transparent)]
pub(crate) struct Unique<'lt, T: ?Sized> {
    inner: Local<'lt, T>,
}

#[allow(unused)]
impl<'lt, T: ?Sized> Local<'lt, T> {
    fn from_non_null(ptr: NonNull<T>) -> Self {
        Local {
            inner: ptr,
            time: AllocTime::default(),
        }
    }

    fn as_ptr(self) -> *mut T {
        self.inner.as_ptr()
    }

    fn as_non_null(self) -> NonNull<T> {
        self.inner
    }

    fn cast<U>(self) -> Local<'lt, U> {
        Local {
            inner: self.inner.cast(),
            time: self.time,
        }
    }

    /// Convert to a shorter lifetime.
    fn lt_relax<'b>(self) -> Local<'lt, T> where 'lt: 'b {
        Local {
            inner: self.inner,
            time: AllocTime::default(),
        }
    }
}

impl<'lt, T> Local<'lt, [T]> {
    fn cast_slice<U>(self) -> Local<'lt, [U]> {
        Local {
            inner: NonNull::new(self.inner.as_ptr() as *mut [U]).unwrap(),
            time: self.time,
        }
    }
}

impl<'lt, T: ?Sized> Unique<'lt, T> {
    pub(crate) unsafe fn new_unchecked(ptr: NonNull<T>) -> Self {
        Self::from_local_unchecked(Local::from_non_null(ptr))
    }

    pub(crate) unsafe fn from_local_unchecked(inner: Local<'lt, T>) -> Self {
        Unique { inner }
    }

    /// Create a unique pointer referring to the uninitialized place.
    pub fn for_value(unique: &'lt mut mem::MaybeUninit<T>) -> Self
    where
        T: Sized
    {
        unsafe {
            Self::from_local_unchecked(Local::from(unique).cast::<T>())
        }
    }

    /// Get a raw pointer to the place.
    pub fn as_ptr(&self) -> *mut T {
        self.inner.as_ptr()
    }
}

impl<'lt, T> Unique<'lt, [T]> {
    /// Create a unique pointer referring to the uninitialized slice.
    pub fn for_slice(unique: &'lt mut [mem::MaybeUninit<T>]) -> Self
    where
        T: Sized
    {
        unsafe {
            Self::from_local_unchecked(Local::from(unique).cast_slice::<T>())
        }
    }
}

impl<T: ?Sized> Clone for Local<'_, T> {
    fn clone(&self) -> Self {
        Local { ..*self }
    }
}

impl<T: ?Sized> Copy for Local<'_, T> {}

impl<'lt, T: ?Sized> From<&'lt T> for Local<'lt, T> {
    fn from(val: &'lt T) -> Self {
        Local {
            inner: NonNull::from(val),
            time: AllocTime::<'lt>::default(),
        }
    }
}

impl<'lt, T: ?Sized> From<&'lt mut T> for Local<'lt, T> {
    fn from(val: &'lt mut T) -> Self {
        Local {
            inner: NonNull::from(val),
            time: AllocTime::<'lt>::default(),
        }
    }
}
