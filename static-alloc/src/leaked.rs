//! This module contains an owning wrapper of a leaked struct.
use alloc_traits::AllocTime;

use core::{
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
};

/// Represents an allocation within a Bump.
///
/// This is an owning pointer comparable to `Box`. It drops the contained value when it is dropped
/// itself. The difference is that no deallocation logic is ever executed.
///
/// # Usage
///
/// This box is the result of allocating from one of the `Bump` allocators using its explicit API.
///
/// ```
/// use static_alloc::Bump;
///
/// ```
///
/// Being a box-like type, an `Option` has the same size.
///
/// ```
/// use core::mem::size_of;
/// use static_alloc::leaked::LeakBox;
///
/// type Boxed = LeakBox<'static, usize>;
/// type Optional = Option<Boxed>;
///
/// assert_eq!(size_of::<Boxed>(), size_of::<Optional>());
/// ```
///
/// TODO: On nightly the inner type should be [unsizable][unsize-coercion].
///
/// [unsize-coercion]: https://doc.rust-lang.org/reference/type-coercions.html#coercion-types
pub struct LeakBox<'ctx, T: ?Sized> {
    #[allow(unused)]
    lifetime: AllocTime<'ctx>,
    // Covariance should be OK.
    pointer: NonNull<T>,
}

impl<'ctx, T> LeakBox<'ctx, T> {
    /// Construct from a raw pointer.
    ///
    /// # Safety
    ///
    /// The allocation must be valid for a write of the value. The memory must also outlive the
    /// lifetime `'ctx` and pointer must not be aliased by any other reference for that scope.
    pub(crate) unsafe fn new_from_raw_non_null(
        pointer: NonNull<T>,
        val: T,
        lifetime: AllocTime<'ctx>,
    ) -> Self {
        // SAFETY:
        // * `ptr` points to an allocation with correct layout for `V`.
        // * It is valid for write as it is the only pointer to it.
        // * The allocation lives for at least `'ctx`.
        core::ptr::write(pointer.as_ptr(), val);
        Self { pointer, lifetime, }
    }
}

impl<'ctx, T> Deref for LeakBox<'ctx, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: constructor guarantees this is initialized and not mutably aliased.
        unsafe { self.pointer.as_ref() }
    }
}

impl<'ctx, T> DerefMut for LeakBox<'ctx, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: constructor guarantees this is initialized and not aliased.
        unsafe { self.pointer.as_mut() }
    }
}

impl<T: ?Sized> Drop for LeakBox<'_, T> {
    fn drop(&mut self) {
        // SAFETY: constructor guarantees this was initialized.
        unsafe { ptr::drop_in_place(self.pointer.as_ptr()) }
    }
}
