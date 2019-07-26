use core::{mem, ptr, slice};
use core::alloc::Layout;
use core::marker::PhantomData;

/// Points to an uninitialized place but would otherwise be a valid reference.
///
/// Makes it possible to deal with uninitialized allocations without requiring an `unsafe` block
/// initializing them and offering a much safer interface for partial initialization and layout
/// calculations than raw pointers.
#[derive(Debug)]
pub struct Uninit<'a, T: ?Sized> {
    /// Pointer to the start of the region.
    ///
    /// Note that `len` is always at least as large as the (minimum) size of `T`. Furthermore, the
    /// pointer is always correctly aligned to a `T`.
    ptr: ptr::NonNull<T>,

    /// The actual length *in bytes*.
    ///
    /// May be larger than required.
    len: usize,

    /// Virtual lifetime to make this behave more similar to references.
    ///
    /// This borrows structures that hand out `Uninit` allocations. Note that this struct is not
    /// `Clone` since it encapsulates an unaliased range within an allocation.
    lifetime: PhantomData<&'a mut T>,
}

/// A non-mutable view on a region used in an `Uninit`.
///
/// Makes it possible to utilize the traversal methods (`split*`, `cast*`, ..) without requiring a
/// mutable reference to the original `Uninit`. It will also never expose mutable pointers or
/// accidentally offer an aliased mutable reference. Prefer this to instead avoiding the borrow of
/// the `Uninit` and manually managing pointers to the region.
#[derive(Debug)]
pub struct UninitView<'a, T: ?Sized>(
    /// The region. The pointer in it must never be dereferenced mutably.
    Uninit<'a, T>,
);

impl Uninit<'_, ()> {
    /// Create a uninit pointer from raw memory.
    ///
    /// ## Safety
    /// A valid allocation must exist at the pointer with length at least `len`. There must be *no*
    /// references aliasing the memory location, and it must be valid to write uninitialized bytes
    /// into arbitrary locations of the region.
    ///
    /// In particular, it is **UB** to create this from a reference to a variable of a type for
    /// which a completely uninitialized content is not valid. The standard type for avoiding the
    /// UB is `core::mem::MaybeUninit`.
    ///
    /// When in doubt, refactor code such that utilization of `from_maybe_uninit` is possible.
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
    pub fn split_layout(self, layout: Layout) -> Result<(Self, Self), Self> {
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

impl<'a> Uninit<'a, ()> {
    /// Split so that the tail is aligned and valid for a `U`.
    pub fn split_cast<U>(self) -> Result<(Self, Uninit<'a, U>), Self> {
        let (this, split) = self.split_layout(Layout::new::<U>())?;
        let cast = split.cast::<U>().ok().unwrap();
        Ok((this, cast))
    }

    pub fn split_slice<U>(self) -> Result<(Self, Uninit<'a, [U]>), Self> {
        let layout = Layout::for_value::<[U]>(&[]);
        let (this, split) = self.split_layout(layout)?;
        let cast = split.cast_slice::<U>().ok().unwrap();
        Ok((this, cast))
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
        // SAFETY:
        // * unaliased for all lifetimes
        // * writing zero uninitialized bytes is well-defined
        let raw = unsafe { Uninit::from_memory(dangling.cast(), 0) };
        raw.cast().unwrap()
    }
}

impl<'a, T> Uninit<'a, T> {
    pub fn from_maybe_uninit(mem: &'a mut mem::MaybeUninit<T>) -> Self {
        let ptr = ptr::NonNull::new(mem.as_mut_ptr()).unwrap();
        let raw = unsafe {
            // SAFETY:
            // * unaliased as we had a mutable reference
            // * can write uninitialized bytes as much as we want
            Uninit::from_memory(ptr.cast(), mem::size_of_val(mem))
        };
        raw.cast().ok().unwrap()
    }

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

    pub fn cast_slice<U>(self) -> Result<Uninit<'a, [U]>, Self> {
        let empty = Layout::for_value::<[U]>(&[]);

        if !self.fits(empty) {
            return Err(self)
        }

        let slice = unsafe {
            // SAFETY: correctly aligned and empty.
            slice::from_raw_parts_mut(self.ptr.cast().as_ptr(), 0)
        };

        Ok(Uninit {
            ptr: slice.into(),
            len: self.len,
            lifetime: PhantomData,
        })
    }

    /// Split off the tail that is not required to hold an instance of `T`.
    pub fn shrink_to_fit(self) -> (Self, Uninit<'a, ()>) {
        // `()` fits every uninit
        let deinit = self.cast::<()>().ok().unwrap();
        // UNWRAP: our own layout fits `T`
        let (minimal, tail) = deinit.split_at(mem::size_of::<T>()).ok().unwrap();
        // UNWRAP: the alignment didn't change, and size is still large enough
        let restored = minimal.cast().ok().unwrap();
        (restored, tail)
    }

    /// Initialize the place and return a reference to the value.
    pub fn init(self, val: T) -> &'a mut T {
        let ptr = self.as_ptr();
        unsafe {
            // SAFETY:
            // * can only create instances where layout of `T` 'fits'
            // * valid for lifetime `'a` (as per unsafe constructor).
            // * unaliased for lifetime `'a` (as per unsafe constructor). No other method
            //   duplicates the pointer or allows a second `Uninit` without borrowing the first.
            //   `UninitView` does not offer this method.
            ptr::write(ptr, val);
            &mut *ptr
        }
    }
}

impl<'a, T> Uninit<'a, [T]> {
    pub fn as_begin_ptr(&self) -> *mut T {
        self.ptr.as_ptr() as *mut T
    }

    pub fn len(&self) -> usize {
        self.size() / mem::size_of::<T>()
    }
}

impl<'a, T: ?Sized> Uninit<'a, T> {
    pub fn borrow(&self) -> UninitView<'_, T> {
        UninitView(Uninit {
            ptr: self.ptr,
            len: self.len,
            lifetime: PhantomData,
        })
    }

    /// Borrow the `Uninit` region for a shorter duration.
    ///
    /// This is the equivalent of `&mut *mut_ref`.
    pub fn borrow_mut(&mut self) -> Uninit<'_, T> {
        Uninit {
            ptr: self.ptr,
            len: self.len,
            lifetime: PhantomData,
        }
    }

    /// Get the byte size of the total allocation.
    pub fn size(&self) -> usize {
        self.len
    }

    /// Acquires the underlying *mut pointer.
    pub fn as_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    /// Acquires the underlying pointer as a `NonNull`.
    pub fn as_non_null(&self) -> ptr::NonNull<T> {
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
impl UninitView<'_, ()> {
    pub fn split_at(self, at: usize) -> Result<(Self, Self), Self> {
        let (head, tail) = self.0.split_at(at).map_err(UninitView)?;
        Ok((UninitView(head), UninitView(tail)))
    }

    /// Split so that the second part fits the layout.
    pub fn split_layout(self, layout: Layout) -> Result<(Self, Self), Self> {
        let (head, tail) = self.0.split_layout(layout).map_err(UninitView)?;
        Ok((UninitView(head), UninitView(tail)))
    }
}

impl<'a> UninitView<'a, ()> {
    /// Split so that the tail is aligned and valid for a `U`.
    pub fn split_cast<U>(self) -> Result<(Self, UninitView<'a, U>), Self> {
        let (this, split) = self.split_layout(Layout::new::<U>())?;
        let cast = split.cast::<U>().ok().unwrap();
        Ok((this, cast))
    }

    pub fn split_slice<U>(self) -> Result<(Self, UninitView<'a, [U]>), Self> {
        let layout = Layout::for_value::<[U]>(&[]);
        let (this, split) = self.split_layout(layout)?;
        let cast = split.cast_slice::<U>().ok().unwrap();
        Ok((this, cast))
    }
}

impl<T> UninitView<'_, T> {
    /// Invent a new uninit allocation for a zero-sized type (ZST).
    ///
    /// # Panics
    /// This method panics when the type parameter is not a zero sized type.
    pub fn invent_for_zst() -> Self {
        UninitView(Uninit::invent_for_zst())
    }
}

impl<'a, T> UninitView<'a, T> {
    pub fn from_maybe_uninit(mem: &'a mem::MaybeUninit<T>) -> Self {
        let ptr = ptr::NonNull::new(mem.as_ptr() as *mut T).unwrap();
        let raw = unsafe {
            // SAFETY:
            // * unaliased as we had a mutable reference
            // * we will not write through the pointer created
            Uninit::from_memory(ptr.cast(), mem::size_of_val(mem))
        };
        UninitView(raw).cast().ok().unwrap()
    }

    pub fn cast<U>(self) -> Result<UninitView<'a, U>, Self> {
        self.0.cast::<U>()
            .map_err(UninitView)
            .map(UninitView)
    }

    pub fn cast_slice<U>(self) -> Result<UninitView<'a, [U]>, Self> {
        self.0.cast_slice::<U>()
            .map_err(UninitView)
            .map(UninitView)
    }

    /// Split off the tail that is not required to hold an instance of `T`.
    pub fn shrink_to_fit(self) -> (Self, UninitView<'a, ()>) {
        let (head, tail) = self.0.shrink_to_fit();
        (UninitView(head), UninitView(tail))
    }
}

impl<'a, T> UninitView<'a, [T]> {
    pub fn as_begin_ptr(&self) -> *const T {
        self.0.as_begin_ptr() as *const T
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, T: ?Sized> UninitView<'a, T> {
    pub fn borrow(&self) -> UninitView<'_, T> {
        self.0.borrow()
    }

    /// Get the byte size of the total allocation.
    pub fn size(&self) -> usize {
        self.0.size()
    }

    /// Acquires the underlying `*const T` pointer.
    pub fn as_ptr(&self) -> *const T {
        self.0.as_ptr() as *const T
    }

    /// Acquires the underlying pointer as a `NonNull`.
    pub fn as_non_null(&self) -> ptr::NonNull<T> {
        self.0.as_non_null()
    }

    /// Dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if" it were actually an
    /// instance of T that is getting borrowed. If a longer lifetime is needed, use `into_ref`.
    ///
    /// ## Safety
    /// The caller must ensure that the content has already been initialized.
    pub unsafe fn as_ref(&self) -> &T {
        self.0.as_ref()
    }

    /// Turn this into a reference to the content.
    ///
    /// ## Safety
    /// The caller must ensure that the content has already been initialized.
    pub unsafe fn into_ref(self) -> &'a T {
        &*self.as_ptr()
    }
}
