#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

/// Fill a collection from an iterator and return remaining iterator.
pub trait Fill<T> {
    fn fill<I>(&mut self, iter: I) -> I::IntoIter
        where I: IntoIterator<Item=T>;
}

#[cfg(feature = "alloc")]
/// Fills the vector as far as possible without reallocating.
impl<T> Fill<T> for alloc::vec::Vec<T> {
    fn fill<I>(&mut self, iter: I) -> I::IntoIter
        where I: IntoIterator<Item=T>
    {
        let mut iter = iter.into_iter();
        for item in iter.by_ref().take(self.capacity() - self.len()) {
            self.push(item);
        }
        iter
    }
}
