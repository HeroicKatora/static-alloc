use core::{fmt, mem, ptr, slice};
use core::alloc::Layout;
use core::marker::PhantomData;

/// Points to an uninitialized place but would otherwise be a valid reference.
///
/// This is a `&mut`-like struct that is somewhat of a pendant to `MaybeUninit`. It makes it
/// possible to deal with uninitialized allocations without requiring an `unsafe` block
/// initializing them and offers a much safer interface for partial initialization and layout
/// calculations than raw pointers.
///
/// Note that it also supports slices which means it does not use `MaybeUninit` internally but
/// offers conversion where necessary.
///
/// ## Usage
///
/// The basic usage is also interacting with `MaybeUninit`:
///
/// ```
/// # #[derive(Default)]
/// # struct MyStruct { };
/// use core::mem::MaybeUninit;
/// use static_alloc::Uninit;
///
/// let mut alloc: MaybeUninit<MyStruct> = MaybeUninit::uninit();
/// let uninit = Uninit::from_maybe_uninit(&mut alloc);
///
/// // notice: no unsafe
/// let instance: &mut MyStruct = uninit.init(MyStruct::default());
/// ```
///
/// But since we are working on arbitrary uninitialized memory it is also possible to reuse the
/// structure for completely arbitrary other types. Just note that there is no integrated mechanis
/// for calling `Drop`.
///
/// ```
/// use core::mem::MaybeUninit;
/// use static_alloc::Uninit;
///
/// // Just a generic buffer.
/// let mut alloc: MaybeUninit<[u32; 1024]> = MaybeUninit::uninit();
/// let uninit = Uninit::from_maybe_uninit(&mut alloc);
///
/// // Now use the first `u32` for a counter:
/// let (counter, tail) = uninit.cast().unwrap().split_to_fit();
/// let counter: &mut u32 = counter.init(0);
///
/// // And some more for a few `u64`.
/// // Note that these are not trivially aligned, but `Uninit` does that for us.
/// let (_, tail) = tail.split_cast().unwrap();
/// let (values, tail) = tail.split_to_fit();
/// let values: &mut [u64; 2] = values.init([0xdead, 0xbeef]);
/// ```
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

/// A non-mutable view on a region used in an [`Uninit`].
///
/// Makes it possible to utilize the traversal methods (`split*`, `cast*`, ..) without requiring a
/// mutable reference to the original `Uninit`. It will also never expose mutable pointers or
/// accidentally offer an aliased mutable reference. Prefer this to instead avoiding the borrow of
/// the `Uninit` and manually managing pointers to the region.
///
/// [`Uninit`]: ./struct.Uninit.html
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

    /// Split the uninit slice at a byte boundary.
    ///
    /// Return `Ok` if the location is in-bounds and `Err` if it is out of bounds.
    pub fn split_at_byte(mut self, at: usize) -> Result<(Self, Self), Self> {
        if self.len < at {
            return Err(self)
        }

        let base = self.ptr.cast::<u8>().as_ptr();
        // SAFETY: by `from_memory`, all offsets `< len` are within the allocation.
        // In particular, no pointer within or one-past-the-end is null.
        let next_base = unsafe { ptr::NonNull::new_unchecked(base.add(at)) };
        let next_len = self.len - at;
        self.len = at;

        // SAFETY:
        // * unaliased because we just clear it.
        // * within one allocation, namely the one we are in.
        let other = unsafe { Self::from_memory(next_base.cast(), next_len) };
        Ok((self, other))
    }

    /// Split so that the second part fits the layout.
    ///
    /// Return `Ok` if this is possible in-bounds and `Err` if it is not.
    pub fn split_layout(self, layout: Layout) -> Result<(Self, Self), Self> {
        let align = self.ptr.cast::<u8>().as_ptr().align_offset(layout.align());
        let aligned_len = self.len.checked_sub(align).and_then(|len| len.checked_sub(layout.size()));

        if aligned_len.is_none() {
            return Err(self)
        }

        let (front, aligned) = self.split_at_byte(align)?;
        assert!(aligned.fits(layout));
        Ok((front, aligned))
    }
}

impl<'a> Uninit<'a, ()> {
    fn decast<T: ?Sized>(uninit: Uninit<'a, T>) -> Self {
        Uninit {
            ptr: uninit.ptr.cast(),
            len: uninit.len,
            lifetime: PhantomData,
        }
    }

    /// Split so that the tail is aligned and valid for a `U`.
    ///
    /// Return `Ok` if this is possible in-bounds (aligned and enough room for at least one `U`)
    /// and `Err` if it is not. The first tuple element is the `Uninit` pointing to the skipped
    /// memory.
    pub fn split_cast<U>(self) -> Result<(Self, Uninit<'a, U>), Self> {
        let (this, split) = self.split_layout(Layout::new::<U>())?;
        let cast = split.cast::<U>().unwrap();
        Ok((this, cast))
    }

    /// Split so that the tail is aligned for a slice `[U]`.
    ///
    /// Return `Ok` if this is possible in-bounds and `Err` if it is not. The first tuple element
    /// is the `Uninit` pointing to the skipped memory.
    ///
    /// The length of the slice is the arbitrary amount that fits into the tail of the allocation.
    /// Note that the length always fulfills the safety requirements for `slice::from_raw_parts`
    /// since the `Uninit` must be contained in a single allocation.
    pub fn split_slice<U>(self) -> Result<(Self, Uninit<'a, [U]>), Self> {
        let layout = Layout::for_value::<[U]>(&[]);
        let (this, split) = self.split_layout(layout)?;
        let cast = split.cast_slice::<U>().unwrap();
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
    /// Create an initializable pointer to the inner bytes of a `MaybeUninit`.
    pub fn from_maybe_uninit(mem: &'a mut mem::MaybeUninit<T>) -> Self {
        let ptr = ptr::NonNull::new(mem.as_mut_ptr()).unwrap();
        let raw = unsafe {
            // SAFETY:
            // * unaliased as we had a mutable reference
            // * can write uninitialized bytes as much as we want
            Uninit::from_memory(ptr.cast(), mem::size_of_val(mem))
        };
        raw.cast().unwrap()
    }

    /// Try to cast to an `Uninit` for another type.
    ///
    /// Return `Ok` if the current `Uninit` is suitably aligned and large enough to hold at least
    /// one `U` and `Err` if it is not. Note that the successful result points to unused remaining
    /// memory behind where the instance can be placed.
    ///
    /// Use [`split_to_fit`] to get rid of surplus memory at the end.
    ///
    /// [`split_to_fit`]: #method.split_to_fit
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

    /// Try to cast to an `Uninit` for a slice type.
    ///
    /// Return `Ok` if the current `Uninit` is suitably aligned and large enough to hold at least
    /// one `U` and `Err` if it is not. Note that the successful result points to unused remaining
    /// memory behind where the instances can be placed.
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

    /// Split off the tail that is not required for holding an instance of `T`.
    pub fn split_to_fit(self) -> (Self, Uninit<'a, ()>) {
        let deinit = Uninit::decast(self);
        // UNWRAP: our own layout fits `T`
        let (minimal, tail) = deinit.split_at_byte(mem::size_of::<T>()).unwrap();
        // UNWRAP: the alignment didn't change, and size is still large enough
        let restored = minimal.cast().unwrap();
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
    /// Get the pointer to the first element of the slice.
    ///
    /// If the slice would be empty then the pointer may be the past-the-end pointer as well.
    pub fn as_begin_ptr(&self) -> *mut T {
        self.ptr.as_ptr() as *mut T
    }

    /// Calculate the theoretical capacity of a slice in the pointed-to allocation.
    pub fn capacity(&self) -> usize {
        self.size()
            .checked_div(mem::size_of::<T>())
            .unwrap_or_else(usize::max_value)
    }

    /// Split the slice at an index.
    ///
    /// This is the pointer equivalent of `slice::split_at`.
    pub fn split_at(self, at: usize) -> Result<(Self, Self), Self> {
        let byte = match at.checked_mul(mem::size_of::<T>()) {
            None => return Err(self),
            Some(byte) if byte > self.len => return Err(self),
            Some(byte) => byte,
        };

        let deinit = Uninit::decast(self);
        let (head, tail) = deinit.split_at_byte(byte).unwrap();
        let head = head.cast_slice().unwrap();
        let tail = tail.cast_slice().unwrap();

        Ok((head, tail))
    }

    /// Split the first element from the slice.
    ///
    /// This is the pointer equivalent of `slice::split_first`.
    pub fn split_first(self) -> Result<(Uninit<'a, T>, Self), Self> {
        self.split_at(1)
            // If it is a valid slice of length 1 it is a valid `T`.
            .map(|(init, tail)| (Uninit::decast(init).cast().unwrap(), tail))
    }

    /// Split the last element from the slice.
    ///
    /// This is the pointer equivalent of `slice::split_last`.
    pub fn split_last(self) -> Result<(Self, Uninit<'a, T>), Self> {
        // Explicitely wrap here: If capacity is 0 then `0 < size_of::<T> ` and the split will fail.
        let split = self.capacity().wrapping_sub(1);
        self.split_at(split)
            // If it is a valid slice of length 1 it is a valid `T`.
            .map(|(head, init)| (head, Uninit::decast(init).cast().unwrap()))
    }
}

impl<'a, T: ?Sized> Uninit<'a, T> {
    /// Borrow a view of the `Uninit` region.
    ///
    /// This is the equivalent of `&*mut_ref as *const _` but never runs afoul of accidentally
    /// creating an actual reference.
    pub fn borrow(&self) -> UninitView<'_, T> {
        UninitView(Uninit {
            ptr: self.ptr,
            len: self.len,
            lifetime: PhantomData,
        })
    }

    /// Borrow the `Uninit` region for a shorter duration.
    ///
    /// This is the equivalent of `&mut *mut_ref as *mut _` but never runs afoul of accidentally
    /// creating an actual reference.
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
    /// Split the uninit view at a byte boundary.
    ///
    /// See [`Uninit::split_at_byte`] for more details.
    ///
    /// [`Uninit::split_at_byte`]: ./struct.Uninit.html#method.split_at_byte
    pub fn split_at_byte(self, at: usize) -> Result<(Self, Self), Self> {
        let (head, tail) = self.0.split_at_byte(at).map_err(UninitView)?;
        Ok((UninitView(head), UninitView(tail)))
    }

    /// Split so that the second part fits the layout.
    ///
    /// See [`Uninit::split_layout`] for more details.
    ///
    /// [`Uninit::split_layout`]: ./struct.Uninit.html#method.split_layout
    pub fn split_layout(self, layout: Layout) -> Result<(Self, Self), Self> {
        let (head, tail) = self.0.split_layout(layout).map_err(UninitView)?;
        Ok((UninitView(head), UninitView(tail)))
    }
}

impl<'a> UninitView<'a, ()> {
    /// Split so that the tail is aligned and valid for a `U`.
    pub fn split_cast<U>(self) -> Result<(Self, UninitView<'a, U>), Self> {
        let (this, split) = self.split_layout(Layout::new::<U>())?;
        let cast = split.cast::<U>().unwrap();
        Ok((this, cast))
    }

    /// Split so that the tail is aligned for a slice `[U]`.
    pub fn split_slice<U>(self) -> Result<(Self, UninitView<'a, [U]>), Self> {
        let layout = Layout::for_value::<[U]>(&[]);
        let (this, split) = self.split_layout(layout)?;
        let cast = split.cast_slice::<U>().unwrap();
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
    /// Create an view to the inner bytes of a `MaybeUninit`.
    ///
    /// This is hardly useful on its own but since `UninitView` mirrors the traversal methods of
    /// `Uninit` it can be used to get pointers to already initialized elements in an immutable
    /// context.
    pub fn from_maybe_uninit(mem: &'a mem::MaybeUninit<T>) -> Self {
        let ptr = ptr::NonNull::new(mem.as_ptr() as *mut T).unwrap();
        let raw = unsafe {
            // SAFETY:
            // * unaliased as we had a mutable reference
            // * we will not write through the pointer created
            Uninit::from_memory(ptr.cast(), mem::size_of_val(mem))
        };
        UninitView(raw).cast().unwrap()
    }

    /// Try to cast to an `UninitView` for another type.
    pub fn cast<U>(self) -> Result<UninitView<'a, U>, Self> {
        self.0.cast::<U>()
            .map_err(UninitView)
            .map(UninitView)
    }

    /// Try to cast to an `UninitView` for a slice type.
    pub fn cast_slice<U>(self) -> Result<UninitView<'a, [U]>, Self> {
        self.0.cast_slice::<U>()
            .map_err(UninitView)
            .map(UninitView)
    }

    /// Split off the tail that is not required for holding an instance of `T`.
    pub fn split_to_fit(self) -> (Self, UninitView<'a, ()>) {
        let (head, tail) = self.0.split_to_fit();
        (UninitView(head), UninitView(tail))
    }
}

impl<'a, T> UninitView<'a, [T]> {
    /// Get the pointer to the first element of the slice.
    pub fn as_begin_ptr(&self) -> *const T {
        self.0.as_begin_ptr() as *const T
    }

    /// Calculate the theoretical capacity of a slice in the pointed-to allocation.
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Split the slice at an index.
    pub fn split_at(self, at: usize) -> Result<(Self, Self), Self> {
        let (head, tail) = self.0.split_at(at).map_err(UninitView)?;
        Ok((UninitView(head), UninitView(tail)))
    }

    /// Split the first element from the slice.
    pub fn split_first(self) -> Result<(UninitView<'a, T>, Self), Self> {
        let (head, tail) = self.0.split_first().map_err(UninitView)?;
        Ok((UninitView(head), UninitView(tail)))
    }

    /// Split the last element from the slice.
    pub fn split_last(self) -> Result<(Self, UninitView<'a, T>), Self> {
        let (head, tail) = self.0.split_last().map_err(UninitView)?;
        Ok((UninitView(head), UninitView(tail)))
    }
}

impl<'a, T: ?Sized> UninitView<'a, T> {
    /// Borrow another view of the `Uninit` region.
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

impl<T: ?Sized> fmt::Debug for Uninit<'_, T> {
   fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
       f.debug_tuple("Uninit")
           .field(&self.ptr)
           .field(&self.len)
           .finish()
   }
}

impl<T: ?Sized> fmt::Debug for UninitView<'_, T> {
   fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
       f.debug_tuple("UninitView")
           .field(&self.0.ptr)
           .field(&self.0.len)
           .finish()
   }
}
