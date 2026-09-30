# Formally verified data structure exercises in Rust

This project is the fruit of an effort to learn formal verification software frameworks in conjunction with the Rust language and mindset. I treat each of two data structures (a bounded vector and a ring buffer) in each of two verification frameworks (Kani and Verus), as well as a custom Option type in Verus. The Verus-verified ring buffer spec was the most interesting and challenging of the exercises, and I would regard it as the meat of the project.

All the code is written in `no_std` rust, meaning that heap allocation is unavailable.

## bvec_kani

Verifying properties of a bounded vector type using Kani. I prove: 
- A push-pop round trip on an empty vector is the identity (`push_pop_round_trip()`).
- An arbitrary sequence of push/pop operations on an empty vector produces a vector of the expected length, as computed by a direct calculation (`apply_operations()`).
- All values are dropped when the vector goes out of scope (`check_drops()`). This is important because the implementation of the vector uses `MaybeUninit`, whose values don't get cleaned up automatically.
- `push` and `pop` follow first-in-last-out semantics (`first_in_last_out()`)
- Panic-freedom and unsafe-access-freedom of all the above is automatically proved by Kani.
Enforced by Kani's bounded nature, all of these proofs use constant bounds. For example, `apply_operations()` uses a sequence of 8 operations on a length-4 vector with loop unwinding.

## ringbuf_kani

Verifying properties of a ring buffer type using Kani. Substantially analogous to the bounded vector. `push_pop_round_trip()`, `apply_operations()` and `check_drops()` are similar to their bounded vector counterparts. The ring buffer follows first-in-first-out semantics, so here we have a `first_in_first_out()` proof.

## option_verus

Verus can't natively reason about `MaybeUninit`, but its standard library contains a `PCell` type that wraps `MaybeUninit`. I use this as the basis of a verified `Option` type whose view is an ordinary Rust `Option`, with fully specced `empty()`, `new()`, `put()`, `borrow()` and `take()` methods.

## bvec_verus

Here it starts to get interesting. I verify the behavior of a bounded vector using Verus, implemented as a fixed-size array of `MyOption` together with a length `len`:
```
pub struct Bvec<T, const N: usize> {
    values: [MyOption<T>; N],
    len: usize,
}
```
 The view is a Verus `Seq`, leveraging the view of `MyOption`. Here I introduce a type invariant: the length of the view must equal the tracked `len`. Verus enforces that any existing `Bvec` adheres to the type invariant. This presents a problem for the `push` and `pop` implementations, where sequentially pushing an element and augmenting the length would violate the type invariant between the two operations. My solution is to mutably borrow `values` and `len` individually for `transact_successful_push` and `transact_successful_pop` functions which mutate them without causing the type invariant check to trigger in between. This allows me to equip `push` and `pop` with verified specs that describe their behavior in terms of the view: for instance,
 ```
     pub fn push(&mut self, t: T) -> (result: Result<(), RingBufAtCapacity>)
        ensures
            old(self)@.len() < N ==> final(self)@.len() == old(self)@.len() + 1 && result.is_ok(), // If the vector is not at capacity, the push is successful and the length increases by 1
            old(self)@.len() == N ==> final(self)@ == old(self)@ && result.is_err(), // If the vector is at capacity, the push fails and the vector is not mutated
        no_unwind // Verus's way of asserting that the function does not panic, not to be confused with Kani's loop unwinding
```

## ringbuf_verus

The Verus ring buffer crate is formally closely analogous to the Verus bounded vector crate, but the proofs are much harder, because I have to dig into Verus's modular arithmetic library to get the proofs to go.
- I track `tail` in addition to `len`; again, the view is a Verus `Seq`, this time counted from the tail and wrapping rather than starting at index 0. 
- I calculate indices to push and pop at using a `safe_add_mod_N` function that performs modular addition verifiably avoiding overflow. 
- Verification of the `push/pop` and `transact_successful_push/pop` functions requires a key lemma proving that a `slot` function that normalizes the index to set the tail at 0 is injective.
- `transact_successful_pop` was the most challenging function to verify. Doing this required a sequence of assertions whose proofs each branched depending on whether the pop caused the tail to wrap around from N - 1 to 0.

## AI declaration

I used AI to answer questions and get advice about Rust, Kani and Verus. The actual work of the project, including the writing of all the code and this readme, was done by hand.

## Other notes

I'm aware of the existence of a [paper](https://arxiv.org/abs/2510.25015) concerning AI-generated verifications of data structures using Verus, using a ring buffer as the main example. I deliberately avoided reading any of the code from the paper while working on this project.