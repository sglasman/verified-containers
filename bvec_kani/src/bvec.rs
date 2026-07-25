use core::mem::MaybeUninit;
use core::ptr;

use shared_nostd::{AtCapacity, PushPop};

pub struct Bvec<T, const N: usize> {
    values: [MaybeUninit<T>; N],
    len: usize,
}

impl<T, const N: usize> Bvec<T, N> {
    pub fn new() -> Self {
        Self {
            values: [const { MaybeUninit::uninit() }; N],
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn capacity(&self) -> usize {
        N
    }

    pub fn push(&mut self, t: T) -> Result<(), AtCapacity> {
        if self.len == N {
            return Err(AtCapacity);
        }
        self.values[self.len].write(t);
        self.len += 1;
        Ok(())
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        unsafe { Some(self.get(self.len)) }
    }

    // SAFETY: Internal use only. If i != len or if the len field is not updated, the bvec will
    // be in an inconsistent state.
    unsafe fn get(&mut self, i: usize) -> T {
        unsafe { ptr::read(self.values[i].as_ptr()) }
    }
}

impl<T, const N: usize> Default for Bvec<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> Drop for Bvec<T, N> {
    fn drop(&mut self) {
        for i in 0..self.len {
            unsafe { drop(self.get(i)) }
        }
    }
}

impl<T, const N: usize> PushPop<T> for Bvec<T, N> {
    fn push(&mut self, t: T) -> Result<(), AtCapacity> {
        self.push(t)
    }

    fn pop(&mut self) -> Option<T> {
        self.pop()
    }
}
