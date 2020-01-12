use core::{alloc, convert};
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

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct EmptyLayoutError;

impl Layout {
    /// Create the layout for a type.
    pub fn new<T>() -> Self {
        Layout(alloc::Layout::new::<T>())
    }

    /// Return the size of the layout.
    pub fn size(&self) -> usize {
        self.0.size()
    }

    /// Return the alignment of the layout.
    pub fn align(&self) -> usize {
        self.0.align()
    }
}

impl NonZeroLayout {
    /// Create the layout for a type.
    ///
    /// This succeeds exactly if the type is not a zero-sized type. Otherwise this constructor
    /// returns `None`.
    pub fn new<T>() -> Option<Self> {
        Self::from_layout(Layout::new::<T>())
    }

    /// Creates a non-empty layout if the given layout is not empty.
    pub fn from_layout(layout: Layout) -> Option<Self> {
        if layout.size() == 0 {
            None
        } else {
            Some(NonZeroLayout(layout))
        }
    }

    /// Return the size of the layout.
    pub fn size(&self) -> NonZeroUsize {
        NonZeroUsize::new(self.0.size()).unwrap()
    }

    /// Return the alignment of the layout.
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

impl convert::TryFrom<Layout> for NonZeroLayout {
    type Error = EmptyLayoutError;

    fn try_from(layout: Layout) -> Result<Self, EmptyLayoutError> {
       NonZeroLayout::from_layout(layout).ok_or(EmptyLayoutError)
    }
}

impl convert::TryFrom<alloc::Layout> for NonZeroLayout {
    type Error = EmptyLayoutError;

    fn try_from(layout: alloc::Layout) -> Result<Self, EmptyLayoutError> {
        NonZeroLayout::try_from(Layout::from(layout))
    }
}
