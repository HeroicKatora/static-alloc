use core::{mem, ptr};
use core::alloc::Layout;
use core::marker::PhantomData;

/// Points to an uninitialized place but would otherwise be a valid reference.
#[derive(Debug)]
pub struct Uninit<'a, T> {
    ptr: ptr::NonNull<T>,
    len: usize,
    lifetime: PhantomData<&'a mut T>,
}

impl Uninit<'_, ()> {
    /// Create a uninit pointer from raw memory.
    ///
    /// ## Safety
    /// A valid, unaliased allocation must exist at the pointer with length at least `len`. It need
    /// *not* be initialized.
    pub unsafe fn from_memory(ptr: ptr::NonNull<()>, len: usize) -> Self {
        Uninit {
            ptr,
            len,
            lifetime: PhantomData,
        }
    }

    pub fn split_at(mut self, at: usize) -> Result<(Self, Self), Self> {
        if self.len < at {
            return Err(self)
        }

        let base = self.ptr.cast::<u8>().as_ptr();
        // SAFETY: by `from_memory`, all offsets `< len` are within the allocation.
        // In particular, no pointer within or one-past-the-end is null.
        let next_base = unsafe { ptr::NonNull::new_unchecked(base.add(at)) };
        let next_len = self.len - at;
        self.len -= at;

        // SAFETY:
        // * unaliased because we just clear it.
        // * within one allocation, namely the one we are in.
        let other = unsafe { Self::from_memory(next_base.cast(), next_len) };
        Ok((self, other))
    }

    /// Split so that the second part fits the layout.
    pub fn split_align(self, layout: Layout) -> Result<(Self, Self), Self> {
        let align = self.ptr.as_ptr().align_offset(layout.align());
        let aligned_len = self.len.checked_sub(align).and_then(|len| len.checked_sub(layout.size()));

        if aligned_len.is_none() {
            return Err(self)
        }

        let (front, aligned) = self.split_at(align)?;
        assert!(aligned.fits(layout));
        Ok((front, aligned))
    }
}

impl<T> Uninit<'_, T> {
    fn fits(&self, layout: Layout) -> bool {
        self.ptr.as_ptr().align_offset(layout.align()) == 0
            && layout.size() <= self.len
    }

    /// Invent a new uninit allocation for a zero-sized type (ZST).
    ///
    /// # Panics
    /// This method panics when the type parameter is not a zero sized type.
    pub fn invent_for_zst() -> Self {
        assert_eq!(mem::size_of::<T>(), 0, "Invented ZST uninit invoked with non-ZST");
        let dangling = ptr::NonNull::<T>::dangling();
        let raw = unsafe { Uninit::from_memory(dangling.cast(), 0) };
        raw.cast().unwrap()
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> Uninit<'a, T> {
    pub fn cast<U>(self) -> Result<Uninit<'a, U>, Self> {
        if !self.fits(Layout::new::<U>()) {
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
