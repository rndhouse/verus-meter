// Release temporary work buffers before storing larger results in a loop.
//
// Each iteration extracts a 64-byte buffer from a temporary staging collection.
// Dropping the collection releases its backing; the extracted buffer remains
// allocated until it too is dropped. Earlier 128-byte results stay allocated
// in the destination across iterations.
// Termination checking is disabled; only the memory bound is specified.
#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// Temporary work storage released within each iteration.
type WorkBuffer = [u8; 64];

// Larger result storage retained across iterations.
type ResultBuffer = [u8; 128];

// Cover the destination handle and two backing slots, two retained results,
// the loop counter, and the result handle used while appending.
spec fn result_stage_budget() -> nat {
    let handle = value_size(Vec<Box<ResultBuffer>>);
    let backing = 2 * value_size(Box<ResultBuffer>);
    let results = 2 * value_size(ResultBuffer);
    let locals = value_size(usize) + value_size(Box<ResultBuffer>);
    handle + backing + results + locals
}

// Build two results within the named allowance by releasing each work buffer first.
// The budget covers both retained results, collection backing, and handles.
// Compare the loop allocation overlap example under expected-failures.
fn main()
    resources peak(memory) <= result_stage_budget(),
{
    let mut destination = Vec::<Box<ResultBuffer>>::with_capacity(2);
    let mut i = 0usize;
    while i < 2 && destination.len() < 2 {
        let mut staging = Vec::<Box<WorkBuffer>>::with_capacity(1);
        let work = Box::new([0u8;64]);
        staging.push(work);
        let old = staging.pop().unwrap();
        drop(staging);
        drop(old);
        let next = Box::new([0u8;128]);
        destination.push(next);
        i += 1;
    }
}

} // verus!
