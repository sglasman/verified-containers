#![no_std]

use core::cell::Cell;

#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Operation<T> {
    Push(T),
    Pop,
}

pub struct DropCounterHolder<'a>(pub &'a Cell<usize>);

impl<'a> Drop for DropCounterHolder<'a> {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct AtCapacity;

pub trait PushPop<T> {
    fn push(&mut self, t: T) -> Result<(), AtCapacity>;
    fn pop(&mut self) -> Option<T>;

    fn apply_operation(&mut self, op: Operation<T>) {
        match op {
            Operation::Push(t) => _ = self.push(t),
            Operation::Pop => _ = self.pop(),
        }
    }
}
