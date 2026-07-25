use common_verus::*;
use option_verus::MyOption;
use vstd::prelude::*;

verus! {

pub struct Bvec<T, const N: usize> {
    values: [MyOption<T>; N],
    len: usize,
}

impl<T, const N: usize> Bvec<T, N> {
    pub fn new() -> Self {
        Self { values: new_my_option_array::<T, N>(), len: 0 }
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

    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        (forall|i: int| 0 <= i < N ==> (i < self.len) == self.values@[i]@.is_some()) && self.len
            <= N
    }

    pub fn push(&mut self, t: T) -> (result: Result<(), BvecAtCapacity>)
        ensures
            old(self)@.len() < N ==> final(self)@.len() == old(self)@.len() + 1 && result.is_ok(),
            old(self)@.len() == N ==> final(self)@ == old(self)@ && result.is_err(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        if self.len == N {
            return Err(BvecAtCapacity);
        }
        Self::transact_successful_push(&mut self.values, &mut self.len, t);
        Ok(())
    }

    pub fn pop(&mut self) -> (result: Result<T, BvecEmpty>)
        ensures
            old(self)@.len() > 0 ==> final(self)@.len() == old(self)@.len() - 1 && result == Ok(
                old(self)@[old(self)@.len() - 1],
            ),
            old(self)@.len() == 0 ==> final(self)@ == old(self)@ && result.is_err(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        if self.len == 0 {
            return Err(BvecEmpty);
        }
        Ok(Self::transact_successful_pop(&mut self.values, &mut self.len))
    }

    fn transact_successful_push(values: &mut [MyOption<T>; N], len: &mut usize, t: T) -> ()
        requires
            *old(len) < N,
            old(values)@[*old(len) as int]@.is_none(),
        ensures
            *final(len) == *old(len) + 1,
            final(values)@[*old(len) as int]@ == Some(t),
            forall|i: int| 0 <= i < N && i != *old(len) ==> final(values)@[i] == old(values)@[i],
        no_unwind
    {
        values[*len].put(t);
        *len += 1;
    }

    fn transact_successful_pop(values: &mut [MyOption<T>; N], len: &mut usize) -> (t: T)
        requires
            0 < *old(len) <= N,
            old(values)@[*old(len) - 1]@.is_some(),
        ensures
            *final(len) == *old(len) - 1,
            final(values)@[*old(len) - 1]@.is_none(),
            t == old(values)@[*old(len) - 1]@.unwrap(),
            forall|i: int|
                0 <= i < N && i != *old(len) - 1 ==> final(values)@[i] == old(values)@[i],
        no_unwind
    {
        let t = values[*len - 1].take();
        *len -= 1;
        t
    }
}

impl<T, const N: usize> View for Bvec<T, N> {
    type V = Seq<T>;

    closed spec fn view(&self) -> Self::V {
        Seq::new(self.len as nat, |i| self.values@[i]@.unwrap())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct BvecAtCapacity;

pub struct BvecEmpty;

} // verus!
