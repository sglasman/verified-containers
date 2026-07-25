use core::mem::MaybeUninit;
use core::ptr;
use shared_nostd::{AtCapacity, PushPop};

pub struct RingBuf<T, const N: usize> {
    values: [MaybeUninit<T>; N],
    head: usize,
    tail: usize,
    len: usize,
}

impl<T, const N: usize> RingBuf<T, N> {
    pub fn new() -> Self {
        Self {
            values: [const { MaybeUninit::uninit() }; N],
            len: 0,
            head: 0,
            tail: 0,
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
        self.values[self.head].write(t);
        self.len += 1;
        self.head = (self.head + 1) % N;
        Ok(())
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        let result = unsafe { Some(self.get(self.tail)) };
        self.tail = (self.tail + 1) % N;
        result
    }

    // SAFETY: Internal use only. If i != len or if the len field is not updated, the bvec will
    // be in an inconsistent state.
    unsafe fn get(&mut self, i: usize) -> T {
        unsafe { ptr::read(self.values[i].as_ptr()) }
    }
}

impl<T, const N: usize> Default for RingBuf<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> Drop for RingBuf<T, N> {
    fn drop(&mut self) {
        for i in self.tail..(self.tail + self.len) {
            unsafe { drop(self.get(i % N)) }
        }
    }
}

impl<T, const N: usize> PushPop<T> for RingBuf<T, N> {
    fn push(&mut self, t: T) -> Result<(), AtCapacity> {
        self.push(t)
    }

    fn pop(&mut self) -> Option<T> {
        self.pop()
    }
}
