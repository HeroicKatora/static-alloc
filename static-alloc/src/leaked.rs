//! This module contains an owning wrapper of a leaked struct.
use alloc_traits::AllocTime;

use core::{
    mem::{ManuallyDrop, MaybeUninit},
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

    /// Remove the value, forgetting the box in the process.
    ///
    /// This is similar to dereferencing a box (`*boxed`) but no deallocation is involved. This
    /// becomes useful when the allocator turns out to have too short of a lifetime.
    ///
    /// # Usage
    ///
    /// You may want to move a long-lived value out of the current scope where it's been allocated.
    ///
    /// ```
    /// # use core::cell::RefCell;
    /// use static_alloc::{Bump, leaked::LeakBox};
    ///
    /// let cell = RefCell::new(0usize);
    ///
    /// let guard = {
    ///     let bump: Bump<[usize; 128]> = Bump::uninit();
    ///
    ///     let mut leaked = bump.boxed(cell.borrow_mut()).unwrap();
    ///     **leaked = 1usize;
    ///
    ///     // Take the value, allowing use independent of the lifetime of bump
    ///     LeakBox::take(leaked)
    /// };
    ///
    /// assert!(cell.try_borrow().is_err());
    /// drop(guard);
    /// assert!(cell.try_borrow().is_ok());
    /// ```
    pub fn take(this: Self) -> T {
        // Do not drop this.
        let this = ManuallyDrop::new(this);
        // SAFETY:
        // * `ptr` points to an initialized allocation according to the constructors of `LeakBox`.
        // * The old value is forgotten and no longer dropped.
        unsafe { core::ptr::read(this.pointer.as_ptr()) }
    }
}

impl<'ctx, T> LeakBox<'ctx, MaybeUninit<T>> {
    /// Write a value into this box, initializing it.
    ///
    /// This can be used to delay the computation of a value until after an allocation succeeded
    /// while maintaining all types necessary for a safe initialization.
    ///
    /// # Usage
    ///
    /// ```
    /// # fn some_expensive_operation() -> [u8; 4] { [0u8; 4] }
    /// # use core::mem::MaybeUninit;
    /// #
    /// # fn fake_main() -> Option<()> {
    /// #
    /// use static_alloc::{Bump, leaked::LeakBox};
    ///
    /// let bump: Bump<[usize; 128]> = Bump::uninit();
    /// let memory = bump.boxed(MaybeUninit::uninit())?;
    ///
    /// let value = LeakBox::write(memory, some_expensive_operation());
    /// # Some(()) } fn main() {}
    /// ```
    pub fn write(mut this: Self, val: T) -> LeakBox<'ctx, T> {
        unsafe {
            // SAFETY: MaybeUninit<T> is valid for writing a T.
            ptr::write(this.as_mut_ptr(), val);
            // SAFETY: initialized by the write before.
            LeakBox::assume_init(this)
        }
    }

    /// Converts to `LeakBox<T>`.
    ///
    /// # Safety
    ///
    /// The value must have been initialized as required by `MaybeUninit::assume_init`. Calling
    /// this when the content is not yet fully initialized causes immediate undefined behavior.
    pub unsafe fn assume_init(this: Self) -> LeakBox<'ctx, T> {
        LeakBox {
            pointer: this.pointer.cast(),
            lifetime: this.lifetime,
        }
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
