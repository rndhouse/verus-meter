// This example shows how the order of releases can keep a loop within a symbolic result
// budget.
//
// Each iteration drops its extracted work buffer before allocating the next, larger
// result. Earlier results stay live in the collection.

#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// Temporary work storage released within each iteration.
type WorkBuffer = [u8; 64];

// Larger result storage retained across iterations.
type ResultBuffer = [u8; 128];

/// `result_budget` counts every retained result and the workspace for the next
/// iteration.
spec fn result_budget(result_count: u32) -> nat {
    // The collection owns a vector of box handles. Each handle points to one result array.
    let handle = value_size(Vec<Box<ResultBuffer>>);
    let backing = (result_count as nat) * value_size(Box<ResultBuffer>);
    let results = (result_count as nat) * value_size(ResultBuffer);
    // The requested count and completed count stay live while the next box is prepared.
    let scalars = 2 * value_size(u32);
    let next = value_size(Box<ResultBuffer>);
    handle + backing + results + scalars + next
}

/// `build_results` releases each temporary buffer before allocating the result that
/// takes its place.
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

/// `main` requests two results within the builder's bound for that input.
fn main()
    resources peak(memory) <= peak(build_results(2)),
{
    let results = build_results(2);
}

} // verus!
