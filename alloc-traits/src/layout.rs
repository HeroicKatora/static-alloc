use core::alloc;
use core::num::NonZeroUsize;

/// Layout of an allocated block of memory.
///
/// Wraps the `Layout` structure from core but extends it in a few ways that would otherwise depend
/// on nightly compiler.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Layout(alloc::Layout);

/// A non-empty layout which can be allocated.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct NonZeroLayout(Layout);

impl Layout {
    pub fn size(&self) -> usize {
        self.0.size()
    }

    pub fn align(&self) -> usize {
        self.0.align()
    }
}

impl NonZeroLayout {
    pub fn new<T>() -> Option<Self> {
        Self::from_layout(alloc::Layout::new::<T>().into())
    }

    pub fn from_layout(layout: Layout) -> Option<Self> {
        if layout.size() == 0 {
            None
        } else {
            Some(NonZeroLayout(layout))
        }
    }

    pub fn size(&self) -> NonZeroUsize {
        NonZeroUsize::new(self.0.size()).unwrap()
    }

    pub fn align(&self) -> usize {
        self.0.align()
    }
}

impl From<Layout> for alloc::Layout {
    fn from(layout: Layout) -> alloc::Layout {
        layout.0
    }
}

impl From<NonZeroLayout> for alloc::Layout {
    fn from(layout: NonZeroLayout) -> alloc::Layout {
        layout.0.into()
    }
}

impl From<alloc::Layout> for Layout {
    fn from(layout: alloc::Layout) -> Layout {
        Layout(layout)
    }
}