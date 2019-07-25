use core::{mem, ptr};
use core::marker::PhantomData;

/// Points to an uninitialized place but would otherwise be a valid reference.
pub struct Uninit<'a, T> {
    ptr: ptr::NonNull<T>,
    len: usize,
    lifetime: PhantomData<&'a mut T>,
}

impl Uninit<'_, ()> {
    pub unsafe fn from_memory(ptr: ptr::NonNull<()>, len: usize) -> Self {
        Uninit {
            ptr,
            len,
            lifetime: PhantomData,
        }
    }
}

impl<'a, T> Uninit<'a, T> {
    pub fn cast<U>(self) -> Result<Uninit<'a, U>, Self> {
        if self.ptr.as_ptr().align_offset(mem::align_of::<U>()) != 0 {
            return Err(self);
        }

        if self.len < mem::size_of::<T>() {
            return Err(self);
        }

        Ok(Uninit {
            ptr: self.ptr.cast(),
            len: self.len,
            lifetime: PhantomData,
        })
    }

    /// Initialize the place and return a reference to the value.
    pub fn init(self, val: T) -> &'a mut T {
        let ptr = self.as_ptr();
        unsafe {
            ptr::write(ptr, val);
            &mut *ptr
        }
    }

    /// Acquires the underlying *mut pointer.
    pub fn as_ptr(self) -> *mut T {
        self.ptr.as_ptr()
    }

    /// Acquires the underlying pointer as a `NonNull`.
    pub fn as_non_null(self) -> ptr::NonNull<T> {
        self.ptr
    }

    /// Dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if" it were actually an
    /// instance of T that is getting borrowed. If a longer lifetime is needed, use `into_ref`.
    pub unsafe fn as_ref(&self) -> &T {
        self.ptr.as_ref()
    }

    /// Mutably dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if" it were actually an
    /// instance of T that is getting borrowed. If a longer lifetime is needed, use `into_mut`.
    pub unsafe fn as_mut(&mut self) -> &mut T {
        self.ptr.as_mut()
    }

    /// Turn this into a reference to the content.
    pub unsafe fn into_ref(self) -> &'a T {
        &*self.as_ptr()
    }

    /// Turn this into a mutable reference to the content.
    pub unsafe fn into_mut(self) -> &'a mut T {
        &mut *self.as_ptr()
    }
}
