/// Assign to a sequence with Fill semantics.
///
/// This struct is crated through the [`IntoIteratorExt::assign`] method. See its documentation for
/// details.
pub struct Assign<I> {
    inner: I,
}

impl<'item, T: 'item, I> Assign<I>
where
    I: ExactSizeIterator + Iterator<Item=&'item mut T>,
{
    pub(crate) fn new(inner: I) -> Self {
        Assign { inner }
    }
}


impl<'item, T: 'item, I>
    crate::Fill<T>
for 
    Assign<I>
where
    I: ExactSizeIterator + Iterator<Item=&'item mut T>,
{
    fn fill<J>(&mut self, iter: J)
        where J: IntoIterator<Item=T>,
    {
        let mut iter = iter.into_iter();
        // Do not use `zip` to control the exact calls to `next`.
        while self.inner.len() != 0 {
            if let Some(item) = iter.next() {
                *self.inner.next().unwrap() = item;
            } else {
                break
            }
        }
    }
}
