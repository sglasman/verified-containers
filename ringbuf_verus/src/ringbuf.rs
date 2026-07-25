use common_verus::*;
use option_verus::MyOption;
use vstd::arithmetic::div_mod::{
    lemma_mod_add_multiples_vanish, lemma_mod_equivalence, lemma_mod_sub_multiples_vanish,
    lemma_small_mod,
};
use vstd::prelude::*;

verus! {

broadcast use vstd::arithmetic::div_mod::group_mod_properties;

pub struct RingBuf<T, const N: usize> {
    values: [MyOption<T>; N],
    len: usize,
    tail: usize,
}

impl<T, const N: usize> RingBuf<T, N> {
    pub fn new() -> Self
        requires
            N > 0,
        ensures
            N > 0,
    {
        proof {
            lemma_small_mod(0, N as nat);
        }
        Self { values: new_my_option_array::<T, N>(), len: 0, tail: 0 }
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

    closed spec fn slot(tail: int, i: int) -> int {
        (tail + i) % N as int
    }

    proof fn slot_inj(tail: int, i: int, j: int)
        requires
            0 <= tail < N,
            0 <= i < N,
            0 <= j < N,
            i != j,
        ensures
            Self::slot(tail, i) != Self::slot(tail, j),
    {
        if Self::slot(tail, i) == Self::slot(tail, j) {
            if i - j > 0 {
                lemma_mod_equivalence(tail + i, tail + j, N as int);
                lemma_small_mod((i - j) as nat, N as nat);
            } else {
                lemma_mod_equivalence(tail + j, tail + i, N as int);
                lemma_small_mod((j - i) as nat, N as nat);
            }
        }
    }

    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        (forall|i: int|
            0 <= i < N ==> (i < self.len) == #[trigger] self.values@[(Self::slot(
                self.tail as int,
                i,
            ))]@.is_some()) && self.len <= N && self.tail < N
    }

    pub fn push(&mut self, t: T) -> (result: Result<(), RingBufAtCapacity>)
        ensures
            old(self)@.len() < N ==> final(self)@.len() == old(self)@.len() + 1 && result.is_ok(),
            old(self)@.len() == N ==> final(self)@ == old(self)@ && result.is_err(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        if self.len == N {
            return Err(RingBufAtCapacity);
        }
        proof {
            assert(self.values@[Self::slot(self.tail as int, self.len as int)]@.is_none());
            assert forall|i: int| 0 <= i < N && i != self.len implies #[trigger] Self::slot(
                self.tail as int,
                i,
            ) != Self::slot(self.tail as int, self.len as int) by {
                Self::slot_inj(self.tail as int, i, self.len as int)
            }
        }
        Self::transact_successful_push(&mut self.values, &mut self.len, &self.tail, t);
        Ok(())
    }

    pub fn pop(&mut self) -> (result: Result<T, RingBufEmpty>)
        ensures
            old(self)@.len() > 0 ==> final(self)@.len() == old(self)@.len() - 1 && result == Ok(
                old(self)@[0],
            ),
            old(self)@.len() == 0 ==> final(self)@ == old(self)@ && result.is_err(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        if self.len == 0 {
            return Err(RingBufEmpty);
        }
        proof {
            assert(self.tail == Self::slot(self.tail as int, 0)) by {
                lemma_small_mod(self.tail as nat, N as nat)
            };
        }
        let t = Self::transact_successful_pop(&mut self.values, &mut self.len, &mut self.tail);
        Ok(t)
    }

    fn transact_successful_push(
        values: &mut [MyOption<T>; N],
        len: &mut usize,
        tail: &usize,
        t: T,
    ) -> ()
        requires
            *old(len) < N,
            *tail < N,
            old(values)@[(*tail + *old(len)) % N as int]@.is_none(),
        ensures
            *final(len) == *old(len) + 1,
            final(values)@[(*tail + *old(len)) % N as int]@ == Some(t),
            forall|i: int|
                0 <= i < N && i != (*tail + *old(len)) % N as int ==> final(values)@[i] == old(
                    values,
                )@[i],
        no_unwind
    {
        values[Self::safe_add_mod_N(*tail, *len)].put(t);
        *len += 1;
    }

    fn transact_successful_pop(
        values: &mut [MyOption<T>; N],
        len: &mut usize,
        tail: &mut usize,
    ) -> (t: T)
        requires
            0 < *old(len) <= N,
            0 <= *old(tail) < N,
            old(values)@[*old(tail) as int]@.is_some(),
            forall|i: int|
                0 <= i < N ==> (i < *old(len)) == old(values)@[Self::slot(
                    *old(tail) as int,
                    i,
                )]@.is_some(),
        ensures
            *final(len) == *old(len) - 1,
            t == old(values)@[*old(tail) as int]@.unwrap(),
            forall|i: int|
                0 <= i < N ==> (i < *final(len)) == final(values)@[Self::slot(
                    *final(tail) as int,
                    i,
                )]@.is_some(),
            *final(tail) == (*old(tail) + 1) % N as int,
        no_unwind
    {
        let t = values[*tail].take();
        *len -= 1;
        *tail = (*tail + 1) % N;
        proof {
            assert(*final(tail) == if *old(tail) < N - 1 {
                *old(tail) + 1
            } else {
                0
            }) by {
                if *old(tail) < N - 1 {
                    lemma_small_mod((*old(tail) + 1) as nat, N as nat)
                } else {
                    lemma_mod_add_multiples_vanish(N as int, N as int);
                }
            };
            assert forall|i: int| 0 <= i < N implies Self::slot(*final(tail) as int, i)
                == Self::slot(*old(tail) as int, i + 1) by {
                if *old(tail) < N - 1 {
                } else {
                    lemma_mod_add_multiples_vanish(i, N as int)
                };
            };
            assert forall|i: int| 0 <= i < N - 1 implies Self::slot(*final(tail) as int, i) != *old(
                tail,
            ) by {
                Self::slot_inj(*old(tail) as int, 0, i + 1);
            }
            assert(Self::slot(*final(tail) as int, N - 1) == *old(tail)) by {
                if *old(tail) < N - 1 {
                    lemma_mod_add_multiples_vanish(*final(tail) as int - 1, N as int);
                    lemma_small_mod((*final(tail) - 1) as nat, N as nat)
                } else {
                    lemma_small_mod((N - 1) as nat, N as nat);
                };
            }
        }
        t
    }

    fn safe_add_mod_N(a: usize, b: usize) -> (result: usize)
        requires
            0 <= a < N,
            0 <= b < N,
        ensures
            result == (a + b) % N as int,
        no_unwind
    {
        if b < N - a {
            proof { lemma_small_mod((a + b) as nat, N as nat) }
            a + b
        } else {
            proof {
                lemma_mod_sub_multiples_vanish(a + b, N as int);
                lemma_small_mod((a + b - N) as nat, N as nat);
            }
            b - (N - a)
        }
    }
}

impl<T, const N: usize> View for RingBuf<T, N> {
    type V = Seq<T>;

    closed spec fn view(&self) -> Self::V {
        Seq::new(self.len as nat, |i| self.values@[(self.tail + i) % N as int]@.unwrap())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct RingBufAtCapacity;

pub struct RingBufEmpty;

} // verus!
