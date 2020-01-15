use core::ptr::NonNull;
use super::{Allocation, Invariant, NonZeroLayout};

pub struct Global;

impl crate::LocalAlloc<'_> for Global {
    fn alloc(&self, layout: NonZeroLayout) -> Option<Allocation<'_>> {
        // SAFETY: the layout is not empty due to `NonZeroLayout`.
        let ptr = unsafe { alloc::alloc::alloc(layout.into()) };
        from_global_ptr(ptr, layout)
    }

    unsafe fn dealloc(&self, alloc: Allocation<'_>) {
        // SAFETY: all preconditions have been propagated.
        alloc::alloc::dealloc(alloc.ptr.as_ptr(), alloc.layout.into())
    }

    unsafe fn alloc_zeroed(&self, layout: NonZeroLayout)
        -> Option<Allocation<'_>> 
    {
        // SAFETY: the layout is not empty due to `NonZeroLayout`.
        let ptr = { alloc::alloc::alloc_zeroed(layout.into()) };
        from_global_ptr(ptr, layout)
    }

    unsafe fn realloc(&self, alloc: Allocation<'_>, layout: NonZeroLayout)
        -> Option<Allocation<'_>>
    {
        // We can't change the alignment, sadly.
        if layout.align() != alloc.layout.align() {
            return None;
        }

        // A new requirement that we did not propagate: We can not allow the new layout to overflow
        // if sized according to its alignment. That is, we should manually check the precondition.
        // For some reason this is not part of the original `alloc` requirements.
        let align_offset = usize::from(layout.size()).wrapping_neg() % layout.align();
        if usize::max_value() - align_offset < layout.size().into() {
            return None;
        }

        let ptr = alloc::alloc::realloc(
            alloc.ptr.as_ptr(),
            alloc.layout.into(),
            layout.size().into());

        from_global_ptr(ptr, layout)
    }
}

fn from_global_ptr<'any>(ptr: *mut u8, layout: NonZeroLayout) -> Option<Allocation<'any>> {
    let ptr = NonNull::new(ptr)?;
    Some(Allocation {
        ptr,
        layout: layout,
        lifetime: Invariant::default(),
    })
}
