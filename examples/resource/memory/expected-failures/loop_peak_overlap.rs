// rust_verify/tests/example.rs expect-failures --- Retaining work overlaps work and result allocations.
// This example shows how delaying a drop can invalidate a loop's peak bound.
//
// The last result is allocated while the extracted work buffer is still live. The
// passing version in `heap/loops/peak_overlap.rs` drops that buffer first.
//
// Look for the two `FAIL:` comments at the result budget and the allocation before the drop.

#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// Temporary work storage released within each iteration.
type WorkBuffer = [u8; 64];

// Larger result storage retained across iterations.
type ResultBuffer = [u8; 128];

/// `result_budget` allows the next result to reuse the temporary work buffer's
/// allowance.
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

/// `build_results` retains the extracted work buffer while allocating its replacement.
fn build_results(result_count: u32) -> Vec<Box<ResultBuffer>>
    // FAIL: The budget assumes the final result can reuse the work buffer's allowance.
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
        // FAIL: The extracted box still owns the work buffer when this result is allocated.
        let next = Box::new([0u8; 128]);
        results.push(next);
        drop(extracted);
        completed += 1;
    }
    results
}

/// `main` requests two results using the builder's claimed bound.
fn main()
    resources peak(memory) <= peak(build_results(2)),
{
    let results = build_results(2);
}

} // verus!
