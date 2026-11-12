// Release temporary work buffers before storing larger results in a loop.
//
// This example shows how release order keeps temporary work and retained
// results within an input-dependent memory budget. Dropping a temporary
// collection releases its backing storage; a buffer extracted from it remains
// allocated until that buffer is also dropped.
#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// Temporary work storage released within each iteration.
type WorkBuffer = [u8; 64];

// Larger result storage retained across iterations.
type ResultBuffer = [u8; 128];

// Cover the collection handle, reserved slots, and retained results, plus
// the input count, loop counter, and next result handle. The count type
// keeps this byte budget representable without extra preconditions.
// During each iteration, room for the next result also covers temporary work.
spec fn result_budget(result_count: u32) -> nat {
    let handle = value_size(Vec<Box<ResultBuffer>>);
    let backing = (result_count as nat) * value_size(Box<ResultBuffer>);
    let results = (result_count as nat) * value_size(ResultBuffer);
    let scalars = 2 * value_size(u32);
    let next = value_size(Box<ResultBuffer>);
    handle + backing + results + scalars + next
}

// Build results by releasing each extracted work buffer before allocating
// its result. Previously completed results remain allocated across iterations.
// Compare the loop allocation overlap example under expected-failures.
fn build_results(result_count: u32) -> Vec<Box<ResultBuffer>>
    resources peak(memory) <= result_budget(result_count),
{
    let mut results = Vec::<Box<ResultBuffer>>::with_capacity(result_count as usize);
    let mut completed = 0u32;
    while completed < result_count {
        let mut staging = Vec::<Box<WorkBuffer>>::with_capacity(1);
        let work = Box::new([0u8; 64]);
        staging.push(work);
        let extracted = staging.pop().unwrap();
        drop(staging);
        drop(extracted);
        let next = Box::new([0u8; 128]);
        results.push(next);
        completed += 1;
    }
    results
}

// Receive results within the builder's allowance for this input.
fn main()
    resources peak(memory) <= peak(build_results(2)),
{
    let results = build_results(2);
}

} // verus!
