#![no_std]
extern crate alloc;

pub mod same;

use alloc::vec::Vec;
pub use crate::same::SameLayout;

/// A dynamically sized buffer for various types.
pub struct BufferVec<T> {
    elements: Vec<T>,
}

/// A temporary view on a BufferVec, with a different element type.
pub struct TempVec<'lt, T> {
    from: &'lt mut dyn DynBufferWith<T>,
    vec: Vec<T>,
}

impl<T> BufferVec<T> {
    pub fn new() -> Self {
        BufferVec::default()
    }

    pub fn with_capacity(cap: usize) -> Self {
        BufferVec {
            elements: Vec::with_capacity(cap),
        }
    }

    /// Use the allocated buffer for a compatible type of elements.
    ///
    /// When the temporary view is dropped the allocation is returned to the buffer. This means its
    /// capacity might be automatically increased, or decreased, based on the used of the vector.
    pub fn use_for<U>(&mut self, marker: SameLayout<T, U>) -> TempVec<'_, U> {
        let from = Wrap::new(&mut self.elements, marker);
        let elements = core::mem::take(&mut from.elements);
        let vec = from.marker.forget_vec(elements);
        TempVec { from, vec, }
    }
}

impl<T> Default for BufferVec<T> {
    fn default() -> Self {
        BufferVec { elements: Vec::new() }
    }
}

impl<T> Drop for TempVec<'_, T> {
    fn drop(&mut self) {
        self.from.swap_internal_with(&mut self.vec);
    }
}

impl<T> core::ops::Deref for TempVec<'_, T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Vec<T> {
        &self.vec
    }
}

impl<T> core::ops::DerefMut for TempVec<'_, T> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        &mut self.vec
    }
}

struct Wrap<T, U> {
    marker: SameLayout<T, U>,
    elements: alloc::vec::Vec<T>,
}

/// Type-erase way for Vec with elements layout compatible to `T`.
trait DynBufferWith<T> {
    fn swap_internal_with(&mut self, _: &mut Vec<T>);
}

impl<T, U> Wrap<T, U> {
    fn new(vec: &mut Vec<T>, _: SameLayout<T, U>) -> &mut Self {
        unsafe { &mut *(vec as *mut _ as *mut Wrap<T, U>) }
    }
}

impl<T, U> DynBufferWith<U> for Wrap<T, U> {
    fn swap_internal_with(&mut self, v: &mut Vec<U>) {
        let mut temp = core::mem::take(v);

        temp.clear();
        let mut temp = self.marker.transpose().forget_vec(temp);
        core::mem::swap(&mut temp, &mut self.elements);

        temp.clear();
        *v = self.marker.forget_vec(temp);
    }
}
