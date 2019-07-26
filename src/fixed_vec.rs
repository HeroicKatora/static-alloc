use core::{ptr, slice};
use crate::uninit::Uninit;

pub struct FixedVec<'a, T> {
    uninit: Uninit<'a, [T]>,
    length: usize,
}

impl<T> FixedVec<'_, T> {
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            // SAFETY: length is the number of initialized elements.
            slice::from_raw_parts(self.uninit.as_begin_ptr(), self.length)
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            // SAFETY:
            // * length is the number of initialized elements.
            // * unaliased since we take ourselves by `mut` and `uninit` does the rest.
            slice::from_raw_parts_mut(self.uninit.as_begin_ptr(), self.length)
        }
    }

    pub fn len(&self) -> usize {
        self.length
    }

    pub fn capacity(&mut self) -> usize {
        self.uninit.capacity()
    }

    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    pub fn push(&mut self, val: T) -> Result<(), T> {
        if self.length == usize::max_value() {
            return Err(val);
        }

        let init = match self.head_tail_mut().1.split_first() {
            Ok((init, _)) => init,
            Err(_) => return Err(val),
        };

        init.init(val);
        self.length += 1;

        Ok(())
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.length == 0 {
            return None;
        }

        let (_, last) = self.head_tail_mut().0.split_last().ok().unwrap();
        let val = unsafe {
            // SAFETY: initialized and no reference of any kind exists to it.
            ptr::read(last.as_ptr())
        };
        self.length -= 1;
        Some(val)
    }

    fn head_tail_mut(&mut self) -> (Uninit<'_, [T]>, Uninit<'_, [T]>) {
        // This must always be possible. `self.length` is nevery greater than the capacity.
        self.uninit.borrow_mut().split_at(self.length).ok().unwrap()
    }
}

impl<'a, T> FixedVec<'a, T> {
    pub fn new(uninit: Uninit<'a, [T]>) -> Self {
        FixedVec {
            uninit,
            length: 0,
        }
    }
}

impl<T> Drop for FixedVec<'_, T> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.as_mut_slice())
        }
    }
}
