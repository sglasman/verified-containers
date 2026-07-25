use crate::bvec::*;
use core::cell::Cell;
use shared_nostd::*;
use std::cmp::min;

#[kani::proof]
fn push_pop_round_trip() {
    let mut bvec = Bvec::<u8, 4>::new();
    let x = kani::any::<u8>();
    bvec.push(x).unwrap();
    let y = bvec.pop().unwrap();
    assert_eq!(x, y);
}

#[kani::proof]
#[kani::unwind(9)]
fn apply_operations() {
    let mut bvec = Bvec::<u8, 4>::new();
    let mut expected_current_len: usize = 0;
    assert_eq!(expected_current_len, bvec.len());
    for _ in 0..8 {
        let op = kani::any::<Operation<u8>>();
        match op {
            Operation::Push(_) => {
                expected_current_len = min(bvec.capacity(), expected_current_len + 1)
            }
            Operation::Pop => {
                expected_current_len = expected_current_len.saturating_sub(1);
            }
        }
        bvec.apply_operation(op);
        assert!(bvec.len() <= bvec.capacity());
        assert_eq!(expected_current_len, bvec.len());
    }
}

#[kani::proof]
#[kani::unwind(5)]
fn check_drops() {
    let cell: Cell<usize> = Cell::new(0);
    let mut expected_drops = 0;
    {
        let mut bvec = Bvec::<DropCounterHolder, 8>::new(); // Will not exceed capacity
        for _ in 0..4 {
            if bvec.len() == 0 || kani::any() {
                bvec.push(DropCounterHolder(&cell)).unwrap();
                expected_drops += 1;
            } else {
                let _ = bvec.pop();
            }
        }
    }
    // All should be dropped, even the ones still in the bvec
    assert_eq!(cell.get(), expected_drops);
}

#[kani::proof]
#[kani::unwind(5)]
fn first_in_last_out() {
    let mut bvec = Bvec::<i8, 8>::new();
    let inputs = kani::any::<[i8; 4]>();
    let mut outputs: Vec<i8> = Vec::new();
    for input in inputs.clone().into_iter() {
        let _ = bvec.push(input);
    }
    for _ in 0..4 {
        outputs.push(bvec.pop().unwrap());
    }
    assert_eq!(inputs.into_iter().rev().collect::<Vec<_>>(), outputs);
}
