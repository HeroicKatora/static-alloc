//! Various utilities such as default implementations.

/// Implementations of default items of traits.
///
/// It is expected that these might be used as a fallback 'super' call of sorts on trait
/// implementors to opportunistically do some form of optimization.
pub mod defaults {
    /// Default implementations for the `LocalAlloc` trait.
    ///
    /// See [`LocalAlloc`] for more information. The methods called by the functions in this module
    /// are documented and will not change between non-breaking releases, if at all. Rather new
    /// variants may be added that call additional methods that might be more efficient. This
    /// avoids accidentally creating a dependency loop in implementors.
    ///
    /// [`LocalAlloc`]: ../../../trait.LocalAlloc.html
    pub mod local {
        use core::ptr::{copy_nonoverlapping, write_bytes};
        use crate::NonZeroLayout;
        use crate::local::{LocalAlloc, Allocation};

        /// Allocate a block of memory initialized with zeros.
        ///
        /// See [`LocalAlloc::alloc_zeroed`] for more information. This is a default implementation
        /// that might be less efficient than a dedicated one. It only uses the `alloc` method.
        ///
        /// [`LocalAlloc::alloc_zeroed`]: ../../../trait.LocalAlloc.html
        pub fn alloc_zeroed<'alloc, Alloc>(
            this: &'alloc Alloc,
            layout: NonZeroLayout
        ) -> Option<Allocation<'alloc>>
        where
            Alloc: LocalAlloc<'alloc> + ?Sized,
        {
            let allocation = this.alloc(layout)?;
            unsafe {
                write_bytes(allocation.ptr.as_ptr(), 0u8, allocation.layout.size().into());
            }
            Some(allocation)
        }

        /// Change the layout of a block previously allocated.
        ///
        /// See [`LocalAlloc::realloc`] for more information. This is a default implementation that
        /// might be less efficient than a dedicated one. It only uses the `alloc` method.
        ///
        /// # Safety
        /// See the trait.
        ///
        /// [`LocalAlloc::realloc`]: ../../../trait.LocalAlloc.html
        pub unsafe fn realloc<'alloc, Alloc>(
            this: &'alloc Alloc,
            alloc: Allocation<'alloc>,
            layout: NonZeroLayout
        ) -> Option<Allocation<'alloc>>
        where
            Alloc: LocalAlloc<'alloc> + ?Sized,
        {
            let new_alloc = this.alloc(layout)?;
            copy_nonoverlapping(
                alloc.ptr.as_ptr(),
                new_alloc.ptr.as_ptr(),
                core::cmp::min(layout.size(), alloc.layout.size()).get());
            Some(new_alloc)
        }
    }
}
