// rust_verify/tests/example.rs expect-failures --- A later iteration overlaps work and result allocations.
// Keep an extracted work buffer alive while allocating its result.
//
// The first iteration fits because no earlier result remains in the destination.
// On the second iteration, a 64-byte work buffer and two 128-byte results exceed
// the result-stage allowance once backing and owning handles are included.
// Compare heap/loops/peak_overlap.rs for the passing release order.
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

// Deliberately retain the extracted buffer until its result is stored.
// The reusable loop check must cover the results retained by earlier iterations.
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
        let next = Box::new([0u8;128]);
        destination.push(next);
        drop(old);
        i += 1;
    }
}

} // verus!
