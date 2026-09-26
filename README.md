# Formally verified data structure exercises in Rust

This project is the fruit of an effort to learn formal verification software frameworks in conjunction with the Rust language and mindset. I treat each of two data structures (a bounded vector and a ring buffer) in each of two verification frameworks (Kani and Verus), as well as a custom Option type in Verus. All the code is written in `no_std` rust, meaning that heap allocation is unavailable.

## bvec_kani

Verifying properties of a bounded vector type using Kani. I prove: 
- A push-pop round trip on an empty vector is the identity (`push_pop_round_trip()`).
- A random sequence of push/pop operations on an empty vector produces a vector of the expected length, as computed by a direct calculation (`apply_operations()`).
- All values are dropped when the vector goes out of scope (`check_drops()`). This is important because the implementation of the vector uses `MaybeUninit`, whose values don't get cleaned up automatically.
- `push` and `pop` follow first-in-last-out semantics (`first_in_last_out()`)
