// rust_verify/tests/example.rs expect-failures --- Retaining work overlaps work and result allocations.
// Keep an extracted work buffer alive while allocating its result.
//
// The allowance has room for results or temporary work. Retaining the work
// buffer while allocating the final result makes their storage overlap and
// exceeds the bound.
// Compare heap/loops/peak_overlap.rs for the passing release order.
// Termination checking is disabled; only the memory bound is specified.
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

// Deliberately retain the extracted buffer until its result is stored.
// The reusable loop check must cover the results retained by earlier iterations.
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
        let next = Box::new([0u8; 128]);
        results.push(next);
        drop(extracted);
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
