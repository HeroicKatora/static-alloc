use core::alloc::{Layout, LayoutErr};
use core::ptr::NonNull;

/// A trait for potentially unsized types whose layout can be derived from a pointer.
///
/// The trait implementation must not lie about this. If the pointer is valid for the layout
/// returned and an instance is placed at the memory pointed to then it must be valid to
/// dereference the pointer and turn it into a shared or mutable reference.
pub unsafe trait PtrLayout {
    /// Get the layout of a pointer pointing to memory for a potentially uninitialized instance.
    fn ptr_layout(_: NonNull<Self>) -> Result<Layout, LayoutErr>;
}

unsafe impl<T> PtrLayout for T {
    fn ptr_layout(_: NonNull<Self>) -> Result<Layout, LayoutErr> {
        Ok(Layout::new::<T>())
    }
}

unsafe impl<T> PtrLayout for [T] {
    fn ptr_layout(ptr: NonNull<Self>) -> Result<Layout, LayoutErr> {
        // Cheat a little. Turn this into a ZST slice but keep the length meta data.
        let deref: *const [()] = ptr.as_ptr() as *const [()];
        // SAFETY: this pointer is not null and the ZST accesses no memory.
        let length = unsafe { (*deref).len() };

        // TODO: replace with array once stable.
        let layout = Layout::new::<T>();
        let from_align = layout.size() & !layout.align();
        // Note on overflow: layout can not overflow when padded to their alignment.
        let pad_to_align = layout.size() + if from_align == 0 { 0 } else {
            layout.align() - from_align 
        };
        match pad_to_align.checked_mul(length) {
            Some(length) => Layout::from_size_align(length, layout.align()),
            None => Err(provoke_layout_err()),
        }
    }
}

unsafe impl PtrLayout for str {
    fn ptr_layout(st: NonNull<Self>) -> Result<Layout, LayoutErr> {
        let slice = NonNull::new(st.as_ptr() as *mut [u8]).unwrap();
        PtrLayout::ptr_layout(slice)
    }
}

fn provoke_layout_err() -> LayoutErr {
    match Layout::from_size_align(usize::max_value(), usize::max_value()) {
        Err(err) => err,
        Ok(_) => unreachable!("Layout with non-power-of-two align should be invalid."),
    }
}

#[cfg(test)]
mod tests {
    use super::PtrLayout;

    use core::alloc::Layout;
    use core::ptr::{NonNull, slice_from_raw_parts_mut};

    #[test]
    fn sized() {
        struct Zst;
        assert_eq!(Ok(Layout::new::<Zst>()), PtrLayout::ptr_layout(NonNull::from(&Zst)));
        assert_eq!(Ok(Layout::new::<usize>()), PtrLayout::ptr_layout(NonNull::from(&0usize)));
    }

    #[test]
    fn slices() {
        struct Zst;
        const ZST_SLICE: &[Zst] = &[Zst, Zst];
        const BYTE_SLICE: &[usize] = &[0, 1];
        const USIZE_SLICE: &[usize] = &[0, 1];

        assert_eq!(Ok(Layout::for_value(ZST_SLICE)), PtrLayout::ptr_layout(NonNull::from(ZST_SLICE)));
        assert_eq!(Ok(Layout::for_value(BYTE_SLICE)), PtrLayout::ptr_layout(NonNull::from(BYTE_SLICE)));
        assert_eq!(Ok(Layout::for_value(USIZE_SLICE)), PtrLayout::ptr_layout(NonNull::from(USIZE_SLICE)));

        let bad_slice = slice_from_raw_parts_mut(1 as *mut usize, usize::max_value());
        let bad_slice = NonNull::new(bad_slice).unwrap();
        assert!(matches!(PtrLayout::ptr_layout(bad_slice), Err(_)));
    }
}
