#![no_std]

use vstd::cell::pcell_maybe_uninit::*;
use vstd::prelude::*;
use vstd::simple_pptr::MemContents;

verus! {

pub struct MyOption<T> {
    value: PCell<T>,
    permission: Tracked<PointsTo<T>>,
}

impl<T> MyOption<T> {
    pub fn empty() -> (myOption: MyOption<T>)
        ensures
            myOption@.is_none(),
    {
        let (value, permission) = PCell::empty();
        Self { value, permission }
    }

    pub fn new(t: T) -> (myOption: MyOption<T>)
        ensures
            myOption@ == Some(t),
    {
        let (value, permission) = PCell::new(t);
        Self { value, permission }
    }

    pub fn put(&mut self, t: T)
        requires
            old(self)@.is_none(),
        ensures
            final(self)@ == Some(t),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        self.value.put(Tracked(self.permission.borrow_mut()), t)
    }

    pub fn borrow(&self) -> (t: &T)
        requires
            self@.is_some(),
    {
        proof {
            use_type_invariant(&*self);
        }
        self.value.borrow(Tracked(self.permission.borrow()))
    }

    pub fn take(&mut self) -> (t: T)
        requires
            old(self)@.is_some(),
        ensures
            t == old(self)@.unwrap() && final(self)@.is_none(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }
        self.value.take(Tracked(self.permission.borrow_mut()))
    }

    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        self.permission@.id() == self.value.id()
    }
}

impl<T> View for MyOption<T> {
    type V = Option<T>;

    closed spec fn view(&self) -> Option<T> {
        match self.permission@.mem_contents() {
            MemContents::Init(t) => Some(t),
            MemContents::Uninit => None,
        }
    }
}

struct OptionAlreadyOccupied;

} // verus!
