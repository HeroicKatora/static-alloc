use core::marker::PhantomData;
use crate::uninit::{Uninit, UninitView};

pub struct Vec<'a, T> {
    uninit: Uninit<'a, ()>,
    phantom: PhantomData<&'a mut [T]>,
}

impl<T> Vec<'_, T> {
    fn inner_regions(&self)
        -> Option<(UninitView<'_, usize>, UninitView<'_, [T]>)>
    {
        let region = self.uninit.borrow();
        let (_, counter) = region.split_cast().ok()?;
        let (counter, tail) = counter.shrink_to_fit();
        let (_, slice) = tail.split_slice().ok()?;
        Some((counter, slice))
    }

    fn inner_regions_mut(&mut self)
        -> Option<(Uninit<'_, usize>, Uninit<'_, [T]>)>
    {
        let region = self.uninit.borrow_mut();
        let (_, counter) = region.split_cast().ok()?;
        let (counter, tail) = counter.shrink_to_fit();
        let (_, slice) = tail.split_slice().ok()?;
        Some((counter, slice))
    }
}

impl<'a, T> Vec<'a, T> {
    pub fn new(uninit: Uninit<'a, ()>) -> Self {
        let mut fixed = Vec {
            uninit,
            phantom: PhantomData,
        };

        if let Some((counter, _)) = fixed.inner_regions_mut() {
            counter.init(0);
        }

        fixed
    }

    pub fn len(&self) -> usize {
        if let Some((counter, _)) = self.inner_regions() {
            unsafe { *counter.as_ptr() }
        } else {
            0
        }
    }

    pub fn as_slice(&self) -> &[T] {
    }
}
