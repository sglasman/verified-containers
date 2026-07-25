use crate::ringbuf::*;
use core::cell::Cell;
use shared_nostd::*;
use std::cmp::min;

#[kani::proof]
fn push_pop_round_trip() {
    let mut ring_buf = RingBuf::<u8, 4>::new();
    let x = kani::any::<u8>();
    ring_buf.push(x).unwrap();
    let y = ring_buf.pop().unwrap();
    assert_eq!(x, y);
}

#[kani::proof]
#[kani::unwind(9)]
fn apply_operations() {
    let mut ring_buf = RingBuf::<u8, 4>::new();
    let mut expected_current_len: usize = 0;
    assert_eq!(expected_current_len, ring_buf.len());
    for _ in 0..8 {
        let op = kani::any::<Operation<u8>>();
        match op {
            Operation::Push(_) => {
                expected_current_len = min(ring_buf.capacity(), expected_current_len + 1)
            }
            Operation::Pop => {
                expected_current_len = expected_current_len.saturating_sub(1);
            }
        }
        ring_buf.apply_operation(op);
        assert!(ring_buf.len() <= ring_buf.capacity());
        assert_eq!(expected_current_len, ring_buf.len());
    }
}

#[kani::proof]
#[kani::unwind(9)]
fn check_drops() {
    let cell: Cell<usize> = Cell::new(0);
    let mut expected_drops = 0;
    {
        let mut ring_buf = RingBuf::<DropCounterHolder, 4>::new();
        for _ in 0..8 {
            if ring_buf.len() == 0 || (kani::any() && ring_buf.len() < 4) {
                ring_buf.push(DropCounterHolder(&cell)).unwrap();
                expected_drops += 1;
            } else {
                let _ = ring_buf.pop();
            }
        }
    }
    // All should be dropped, even the ones still in the ring_buf
    assert_eq!(cell.get(), expected_drops);
}

#[kani::proof]
#[kani::unwind(8)]
fn first_in_first_out() {
    let mut ring_buf = RingBuf::<i8, 2>::new();
    let inputs = kani::any::<[i8; 4]>();
    let mut inputs_iter = inputs.clone().into_iter().peekable();
    let mut outputs: Vec<i8> = Vec::new();
    while inputs_iter.peek().is_some() {
        if ring_buf.len() == 0 || (kani::any() && ring_buf.len() < ring_buf.capacity()) {
            let _ = ring_buf.push(inputs_iter.next().unwrap());
        } else {
            outputs.push(ring_buf.pop().unwrap());
        }
    }
    while let Some(t) = ring_buf.pop() {
        outputs.push(t)
    }
    assert_eq!(inputs.into_iter().collect::<Vec<_>>(), outputs);
}
