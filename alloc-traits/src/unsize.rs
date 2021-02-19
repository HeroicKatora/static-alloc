//! This module encapsulates correct coercers and coercible pointers.
//!
//! The act of Coercion, a special kind of somewhat trivial pointer conversion, is not exposed as a
//! _safe_ trait. There are two unsafe traits: The first captures which structs unsized to which
//! dynamically sized types; which the second is applied to (wrappers around) pointers that can be
//! coerced implicitly.
//!
//! We do not have the luxury of compiler builtin checks to enforce that a particular pointer
//! conversion is sound, nor can we generate the tag of target fat pointer from thin air. Instead,
//! we use a trick. Note that both of these safety issues occur in the context of the pointer
//! conversion. Now, we can require the _user_ to _unsafely_ provide a function that implements the
//! conversion correctly. The _using_ this function is safe and enables any particular user-defined
//! pointer wrapper to safely transform itself. Note that for a limited selection of standard
//! traits we can even go so far as offer pre-built converters that are safe to use in general.
#![allow(unused_unsafe)] // Err on the side of caution.
use core::alloc::Layout;

mod impls {
    //! Safety: Provenance is always the same as self, pointer target is simply passed through.
    use core::ptr::NonNull;
    use super::CoerciblePtr;

    unsafe impl<'lt, T, U: ?Sized + 'lt> CoerciblePtr<U> for &'lt T {
        type Pointee = T;
        type Output = &'lt U;
        fn as_sized_ptr(&self) -> *mut T {
            (*self) as *const T as *mut T
        }
        unsafe fn replace_ptr(self, new: *mut U) -> &'lt U {
            unsafe { &*new }
        }
    }

    /// Safety: Provenance is always the same as self.
    unsafe impl<'lt, T, U: ?Sized + 'lt> CoerciblePtr<U> for &'lt mut T {
        type Pointee = T;
        type Output = &'lt mut U;
        fn as_sized_ptr(&self) -> *mut T {
            (*self) as *const T as *mut T
        }
        unsafe fn replace_ptr(self, new: *mut U) -> &'lt mut U {
            unsafe { &mut *new }
        }
    }

    unsafe impl<Ptr, U, T> CoerciblePtr<U> for core::pin::Pin<Ptr>
    where
        Ptr: CoerciblePtr<U> + core::ops::Deref<Target=T>,
        Ptr::Output: core::ops::Deref<Target=T>,
    {
        type Pointee = T;
        type Output = core::pin::Pin<Ptr::Output>;
        fn as_sized_ptr(&self) -> *mut Self::Pointee {
            self.as_ref().get_ref() as *const Self::Pointee as *mut _
        }
        unsafe fn replace_ptr(self, new: *mut U) -> Self::Output {
            let inner = core::pin::Pin::into_inner_unchecked(self);
            let new = inner.replace_ptr(new);
            core::pin::Pin::new_unchecked(new)
        }
    }

    unsafe impl<T, U: ?Sized> CoerciblePtr<U> for core::ptr::NonNull<T> {
        type Pointee = T;
        type Output = NonNull<U>;
        fn as_sized_ptr(&self) -> *mut T {
            self.as_ptr()
        }
        unsafe fn replace_ptr(self, new: *mut U) -> NonNull<U> {
            // Safety: 
            NonNull::new_unchecked(new)
        }
    }
}

/// Enables the unsizing of a sized pointer.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Coercion<T, U: ?Sized> {
    coerce: fn(*const T) -> *const U,
}

/// A stateful coercion of a sized pointer.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct CoercionWith<'lt, T, U: ?Sized> {
    coerce: &'lt dyn Fn(*const T) -> *const U,
}

impl<T, U: ?Sized> Coercion<T, U> {
    /// Construct a new coercer.
    ///
    /// # Safety
    ///
    /// The method must not perform any action other than unsizing the pointer.
    ///
    /// # Usage
    ///
    /// ```
    /// use alloc_traits::Coercion;
    /// use core::fmt::Debug;
    ///
    /// let c: Coercion<u32, dyn Debug> = unsafe {
    ///     Coercion::new(|x| x)
    /// };
    /// ```
    pub unsafe fn new(coerce: fn(*const T) -> *const U) -> Self {
        Coercion { coerce }
    }
}

macro_rules! coerce_to_dyn_trait {
    ($(#[$attr:meta])* fn $name:ident() -> $trait_type:path) => {
        impl<'lt, T: $trait_type + 'lt> Coercion<T, dyn $trait_type + 'lt> {
            $(#[$attr])*
            pub fn $name() -> Self {
                fn coerce_to_that_type<'lt, T: $trait_type + 'lt>(
                    ptr: *const T
                ) -> *const (dyn $trait_type + 'lt) {
                    ptr
                }

                Coercion { coerce: coerce_to_that_type }
            }
        }
    };

    /* TODO: figure out how to make this work.
     * Then add Iterator<Item=U>, PartialEq<Rhs>, PartialOrd<Rhs>, etc.
    ($(#[$attr:meta])* fn $name:ident<$($param:ident),*>() -> $trait_type:ty) => {
        impl<'lt, $($param),*, T: $trait_type + 'lt> Coercion<T, dyn ($trait_type + 'lt)> {
            $(#[$attr])*
            pub fn $name() -> Self {
                fn coerce_to_that_type<'lt, $($param),*, T: $trait_type + 'lt>(
                    ptr: *const T
                ) -> *const (dyn $trait_type + 'lt) {
                    ptr
                }

                Coercion { coerce: coerce_to_that_type }
            }
        }
    };
    */
}

coerce_to_dyn_trait!(
    /// Create a coercer that unsizes and keeps dynamic type information.
    ///
    /// # Usage
    ///
    /// ```
    /// use alloc_traits::{Coercion, CoerceUnsize};
    /// use core::any::Any;
    ///
    /// fn generic<T: Any>(ptr: &T) -> &dyn Any {
    ///     ptr.unsize(Coercion::to_any())
    /// }
    /// ```
    fn to_any() -> core::any::Any
);

coerce_to_dyn_trait!(
    /// Create a coercer that unsizes a parameter to dynamically debug its fields.
    ///
    /// # Usage
    ///
    /// ```
    /// use alloc_traits::{Coercion, CoerceUnsize};
    /// use core::fmt::Debug;
    ///
    /// fn generic<T: Debug>(ptr: &T) -> &dyn Debug {
    ///     ptr.unsize(Coercion::to_debug())
    /// }
    /// ```
    fn to_debug() -> core::fmt::Debug
);

coerce_to_dyn_trait!(
    /// Create a coercer that unsizes a parameter to display it.
    ///
    /// # Usage
    ///
    /// ```
    /// use alloc_traits::{Coercion, CoerceUnsize};
    /// use core::fmt::Display;
    ///
    /// fn generic<T: Display>(ptr: &T) -> &dyn Display {
    ///     ptr.unsize(Coercion::to_display())
    /// }
    /// ```
    fn to_display() -> core::fmt::Display
);

#[cfg(rustc_1_51)]
impl<T, const N: usize> Coercion<[T; N], [T]> {
    /// Create a coercer that unsizes an array to a slice.
    ///
    /// # Usage
    ///
    /// ```
    /// use alloc_traits::{Coercion, CoerceUnsize};
    /// use core::fmt::Display;
    ///
    /// fn generic<T>(ptr: &[T; 2]) -> &[T] {
    ///     ptr.unsize(Coercion::to_slice())
    /// }
    /// ```
    pub fn to_slice() -> Self {
        fn coerce<T, const N: usize>(
            ptr: *const [T; N]
        ) -> *const [T] { ptr }
        Coercion { coerce }
    }
}

/// Add unsizing methods to pointer-like types.
///
/// # Safety
/// A correct implementation must uphold, when calling `replace_ptr` with valid arguments, that the
/// pointer target and the provenance of the pointer stay unchanged. This allows calling the
/// coercion of inner fields of wrappers even when an invariant depends on the pointer target.
pub unsafe trait CoerciblePtr<U: ?Sized>: Sized {
    /// The type we point to.
    /// This influences which kinds of unsizing are possible.
    type Pointee;
    /// The output type when unsizing the pointee to `U`.
    type Output;
    /// Get the raw inner pointer.
    fn as_sized_ptr(&self) -> *mut Self::Pointee;
    /// Replace the container inner pointer with an unsized version.
    /// # Safety
    /// The caller guarantees that the replacement is the same pointer, just a fat pointer variant
    /// with a correct tag.
    unsafe fn replace_ptr(self, _: *mut U) -> Self::Output;
}

/// An extension trait using `CoerciblePtr` for a safe interface.
pub trait CoerceUnsize<U: ?Sized>: CoerciblePtr<U> {
    /// Convert a pointer, as if with unsize coercion.
    ///
    /// See [`CoerciblePtr::unsize_with`][unsize_with] for details.
    ///
    /// [unsize_with]: struct.CoerciblePtr.html#method.unsize_with
    fn unsize(self, with: Coercion<Self::Pointee, U>) -> Self::Output {
        unsafe {
            let ptr = self.as_sized_ptr();
            let new_ptr = unsize_with(ptr, with.coerce);
            self.replace_ptr(new_ptr)
        }
    }

    /// Convert a pointer, as if with unsize coercion.
    ///
    /// See [`CoerciblePtr::unsize_with`][unsize_with] for details.
    ///
    /// [unsize_with]: struct.CoerciblePtr.html#method.unsize_with
    fn unsize_with(self, with: CoercionWith<Self::Pointee, U>) -> Self::Output {
        unsafe {
            let ptr = self.as_sized_ptr();
            let new_ptr = unsize_with(ptr, with.coerce);
            self.replace_ptr(new_ptr)
        }
    }
}

impl<T, U: ?Sized> CoerceUnsize<U> for T
where
    T: CoerciblePtr<U>
{}

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
unsafe fn unsize_with<T, U: ?Sized>(
    ptr: *mut T,
    with: impl Fn(*const T) -> *const U,
) -> *mut U {
    let mut raw_unsized = with(ptr) as *mut U;

    debug_assert_eq!(Layout::for_value(&raw_unsized), Layout::new::<[usize; 2]>(),
        "Unexpected layout of unsized pointer.");
    debug_assert_eq!(raw_unsized as *const u8 as usize, ptr as usize,
        "Unsize coercion seemingly changed the pointer base");

    let ptr_slot = &mut raw_unsized as *mut *mut U as *mut *const u8;
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
    unsafe { ptr_slot.write(ptr as *const u8) };

    // Safety: the base pointer that we've just written was not null.
    raw_unsized
}

/// Ensure that using `CoerceUnsize` does not import as_sized_ptr.
///
/// ```compile_fail
/// use alloc_traits::CoerceUnsize;
/// use core::ptr::NonNull;
///
/// let ptr = NonNull::from(&2u32);
/// let _ = ptr.as_sized_ptr();
/// ```
extern {}
