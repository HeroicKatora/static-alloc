#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

/// Fill a collection from an iterator until a capacity has been reached.
pub trait Fill<T> {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=T>;

    fn fill_and_spill<I>(&mut self, iter: I) -> I::IntoIter
        where I: IntoIterator<Item=T>
    {
        let mut iter = iter.into_iter();
        self.fill(&mut iter);
        iter
    }
}

#[cfg(feature = "alloc")]
/// Fills the vector as far as possible without reallocating.
impl<T> Fill<T> for alloc::vec::Vec<T> {
    fn fill<I>(&mut self, iter: I) -> I::IntoIter
        where I: IntoIterator<Item=T>
    {
        for item in iter.take(self.capacity() - self.len()) {
            self.push(item);
        }
    }
}

#[cfg(feature = "alloc")]
/// Fills the queue as far as possible without reallocating.
impl<T> Fill<T> for alloc::collections::VecDeque<T> {
    fn fill<I>(&mut self, iter: I) -> I::IntoIter
        where I: IntoIterator<Item=T>
    {
        for item in iter.take(self.capacity() - self.len()) {
            self.push_back(item);
        }
    }
}

/// Consumes all items until the first `None`.
impl Fill<()> for () {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=()>
    {
        for () in iter { }
    }
}

/// If the option does not yet contain an item, insert the next item of the iterator.
///
/// Note that this will call `iter.next()` at most once. The option will still be empty if the
/// iterator is not fused and returns `None` as the first result of that call.
impl<T> Fill<T> for Option<T> {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=T>
    {
        let mut iter = iter.into_iter();
        match self {
            None => *self = iter.next(),
            Some(_) => (),
        }
    }
}

/// Tries to fill the container in the `Ok`.
///
/// A result is full if it contains an error, or if the container in `Ok` is full.
impl<C, E, T> Fill<Result<T, E>> for Result<C, E>
    where C: Fill<T>,
{
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=Result<T, E>>
    {
        let mut iter = iter.into_iter();

        let container = match self {
            Ok(container) => container,
            Err(_) => return,
        };

        let err = loop {
            match iter.next() {
                None => return,
                Some(Err(err)) => break err,
                Some(Ok(ok)) => {
                    container.fill(core::iter::once(ok));
                },
            };
        };

        *self = Err(err);
    }
}

/// Advances self while inserting elements from the iterator.
impl<T> Fill<T> for core::slice::IterMut<'_, T> {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=T>
    {
        let mut iter = iter.into_iter();
        // Do not use `zip` to control the exact calls to `next`.
        while self.len() != 0 {
            if let Some(item) = iter.next() {
                *self.next().unwrap() = item;
            } else {
                break
            }
        }
    }
}

/// Advances self while swapping elements with the iterator.
impl<'a, T: 'a> Fill<&'a mut T> for core::slice::IterMut<'_, T> {
    fn fill<I>(&mut self, iter: I)
        where I: IntoIterator<Item=&'a mut T>
    {
        let mut iter = iter.into_iter();
        // Do not use `zip` to control the exact calls to `next`.
        while self.len() != 0 {
            if let Some(item) = iter.next() {
                core::mem::swap(self.next().unwrap(), item);
            } else {
                break
            }
        }
    }
}
