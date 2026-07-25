use option_verus::MyOption;
use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub fn new_my_option_array<T, const N: usize>() -> (arr: [MyOption<T>; N])
    ensures
        forall|i: int| 0 <= i < N ==> arr@[i]@.is_none(),
{
    core::array::from_fn(|_| MyOption::empty())
}

} // verus!
