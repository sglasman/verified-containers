#![cfg_attr(not(any(test, kani)), no_std)]

mod bvec;

#[cfg(kani)]
mod proofs;
