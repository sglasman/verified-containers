#![cfg_attr(not(any(test, kani)), no_std)]

mod ringbuf;

#[cfg(kani)]
mod proofs;
