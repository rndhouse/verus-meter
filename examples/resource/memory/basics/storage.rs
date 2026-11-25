// This example shows how the lifetimes of local arrays determine peak memory.
//
// Separate scopes, exclusive branches, and successive iterations can reuse workspace.
// Two arrays in the same scope can require twice as much. Proof-only arrays add no
// executable storage.

use vstd::prelude::*;

verus! {

/// `separate_scopes` uses one array's allowance across two successive scopes.
///
/// A stage's workspace stops contributing once its scope ends, so the budget
/// only needs to cover one array at a time.
fn separate_scopes()
    resources peak(memory) <= value_size([u32; 64]),
{
    // Explicit scopes make the reuse independent of compiler optimizations.
    { let first = [0u32; 64]; }
    { let second = [0u32; 64]; }
}

/// `overlapping_scopes` keeps both arrays live when allocating the second.
///
/// Both declared arrays remain live while the second is initialized. The budget
/// covers exactly those two arrays.
fn overlapping_scopes()
    resources peak(memory) <= 2 * value_size([u32; 64]),
{
    let first = [0u32; 64];
    // The first slot stays live until this function's block ends, even if unused.
    let second = [0u32; 64];
}

/// `branches` bounds both alternatives with the flag and the larger array.
///
/// Only one alternative runs, so their workspace costs are not added together.
/// The budget covers the larger branch while retaining the condition's storage.
fn branches(condition: bool)
    resources peak(memory) <= value_size(condition) + value_size([u32; 64]),
{
    if condition {
        let scratch = [0u32; 64];
    } else {
        let scratch = [0u32; 32];
    }
}

/// `reusable_loop` reuses an iteration's workspace after its scope ends.
///
/// Workspace whose lifetime ends with an iteration can be reused by the next.
/// Termination is a separate obligation, established by the decreasing expression.
/// The condition remains live while each iteration uses its workspace.
fn reusable_loop(mut condition: bool)
    resources peak(memory) <= value_size(condition) + value_size([u32; 64]),
{
    while condition
        decreases if condition { 1int } else { 0int },
    {
        let scratch = [0u32; 64];
        condition = false;
    }
}

/// `erased_proof_data` shows that only the executable scratch array contributes to the
/// bound.
///
/// Ghost and proof data are erased, so even these deliberately large proof-only
/// arrays leave the executable workspace's budget unchanged.
fn erased_proof_data()
    resources peak(memory) <= value_size([u32; 64]),
{
    let ghost large = [0u32; 4096usize];
    proof { let another = [0u32; 8192usize]; }
    let scratch = [0u32; 64];
}

/// `main` leaves each workspace pattern to be verified under its own contract.
fn main() {}

}
