use core::{alloc::Layout, ptr::NonNull};

mod impls {
    use core::ptr::NonNull;
    use super::{CoerceUnsize, unsize_with};

    unsafe impl<'lt, T, U: ?Sized + 'lt> CoerceUnsize<U> for &'lt T {
        type Pointee = T;
        type Output = &'lt U;
        unsafe fn unsize_with<F: Fn(&T) -> &U>(self, with: F) -> Self::Output {
            &*unsize_with(NonNull::from(self), with).as_ptr()
        }
    }

    unsafe impl<'lt, T, U: ?Sized + 'lt> CoerceUnsize<U> for &'lt mut T {
        type Pointee = T;
        type Output = &'lt mut U;
        unsafe fn unsize_with<F: Fn(&T) -> &U>(self, with: F) -> Self::Output {
            &mut *unsize_with(NonNull::from(self), with).as_ptr()
        }
    }

    /* TODO: this actually does _not_ seem self-evident.
     * Quite the opposite, the requirements on `with` might be stronger. But consider that we only
     * pass a shared reference so maybe my worries are over nothing.
    impl<Ptr, U> CoerceUnsize<U> for core::pin::Pin<Ptr>
    where
        Ptr: CoerceUnsize<U>
    {
        type Output = core::pin::Pin<Ptr::Output>;
        unsafe fn unsize_with(self, with: impl Fn(&Self) -> &U) -> Self::Output {
            self.into_inner_unchecked()
        }
    }
    */

    unsafe impl<T, U: ?Sized> CoerceUnsize<U> for core::ptr::NonNull<T> {
        type Pointee = T;
        type Output = NonNull<U>;
        unsafe fn unsize_with<F: Fn(&T) -> &U>(self, with: F) -> Self::Output {
            unsize_with(NonNull::from(self), with)
        }
    }
}

/// Enables the unsizing of a sized pointer.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct CoerciblePtr<T> {
    ptr: NonNull<T>,
}

/// Add unsizing methods to pointer-like types.
pub unsafe trait CoerceUnsize<U: ?Sized>: Sized {
    /// The type we point to.
    /// This influences which kinds of unsizing are possible.
    type Pointee;
    /// The output type when unsizing the pointee to `U`.
    type Output;
    /// Convert a pointer, as if with unsize coercion.
    ///
    /// See [`CoerciblePtr::unsize_with`][unsize_with] for details.
    ///
    /// [unsize_with]: struct.CoerciblePtr.html#method.unsize_with
    unsafe fn unsize_with<F: Fn(&Self::Pointee) -> &U>(self, with: F) -> Self::Output;
}

impl<T> CoerciblePtr<T> {
    /// Get the contained pointer as a `NonNull`.
    pub fn get(self) -> NonNull<T> {
        self.ptr
    }

    /// Get the contained pointer.
    pub fn as_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    /// Convert a pointer, as if with unsize coercion.
    ///
    /// The result pointer will have the same provenance information as the argument `ptr`.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that it is sound to dereference the argument and convert it into a
    /// reference. This also, very slightly, relies on some of Rust's internal layout but it will
    /// assert that they actually hold. If this sounds too risky, do not use this method. The caller
    /// must also guarantee that `with` will only execute a coercion and _not_ change the pointer
    /// itself.
    ///
    /// # Usage
    ///
    /// ```
    ///
    /// ```
    pub unsafe fn unsize_with<U: ?Sized>(self, with: impl Fn(&T) -> &U) -> NonNull<U> {
        unsize_with(self.ptr, with)
    }
}

/// Convert a pointer, as if with unsize coercion.
///
/// The result pointer will have the same provenance information as the argument `ptr`.
///
/// # Safety
///
/// The caller must guarantee that it is sound to dereference the argument and convert it into a
/// reference. This also, very slightly, relies on some of Rust's internal layout but it will
/// assert that they actually hold. If this sounds too risky, do not use this method. The caller
/// must also guarantee that `with` will only execute a coercion and _not_ change the pointer
/// itself.
#[allow(unused_unsafe)] // Err on the side of caution.
unsafe fn unsize_with<T, U: ?Sized>(
    ptr: NonNull<T>,
    with: impl Fn(&T) -> &U,
) -> NonNull<U> {
    let raw = ptr.as_ptr();

    let mut raw_unsized = {
        // Safety: caller upholds this directly.
        let temp_reference = unsafe { &*raw };
        with(temp_reference) as *const U
    };

    debug_assert_eq!(Layout::for_value(&raw_unsized), Layout::new::<[usize; 2]>(),
        "Unexpected layout of unsized pointer.");
    debug_assert_eq!(raw_unsized as *const u8 as usize, raw as usize,
        "Unsize coercion seemingly changed the pointer base");

    let ptr_slot = &mut raw_unsized as *mut *const U as *mut *const u8;
    // Safety: Not totally clear as it relies on the standard library implementation of pointers.
    // The layout is usually valid for such a write (we've asserted that above) and all pointers
    // are larger and at least as aligned as a single pointer to bytes.
    // It could be that this invalidates the representation of `raw_unsized` but all currently
    // pointers store their tag _behind_ the base pointer.
    //
    // There is an `unsafe`, unstable method (#75091) with the same effect and implementation.
    //
    // According to the `ptr::set_ptr_value` method we change provenance back to the `raw` pointer.
    // This can be used since we haven't used any pointer from which it was derived. This
    // invalidates the access tags of `temp_reference` and the original `raw_unsized` value but
    // both will no longer be used.
    unsafe { ptr_slot.write(raw as *const u8) };

    // Safety: the base pointer that we've just written was not null.
    unsafe { NonNull::new_unchecked(raw_unsized as *mut U) }
}
