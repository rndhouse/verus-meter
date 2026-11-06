// Shows how reusing workspace can reduce a program's memory needs.
//
// Memory needs depend on which pieces of work overlap, rather than how much work
// is done in total. These small examples isolate that distinction and show why
// proof-only data can be excluded from the runtime budget.
// Budgets use abstract model bytes; they do not predict physical stack sizes.
// mem_size names a type or parameter's storage; mem_peak names a function's bound.
// Run with --trace to inspect the accounting behind each bound.

use vstd::prelude::*;

verus! {

// Demonstrates that separate stages of work can share the same memory budget.
//
// A stage's workspace stops contributing once its scope ends, so the budget
// only needs to cover one array at a time.
// The initializer uses the declared array's storage.
fn separate_scopes()
    mem_peak <= mem_size([u32; 64]),
{
    // Explicit scopes make the reuse independent of compiler optimizations.
    { let first = [0u32; 64]; }
    { let second = [0u32; 64]; }
}

// Demonstrates why keeping two workspaces alive increases peak memory use.
//
// Both declared arrays remain live while the second is initialized. The budget
// covers exactly those two arrays.
fn overlapping_scopes()
    mem_peak <= 2 * mem_size([u32; 64]),
{
    let first = [0u32; 64];
    // The first slot stays live until this function's block ends, even if unused.
    let second = [0u32; 64];
}

// Bounds memory for a choice between two ways of doing the same work.
//
// Only one alternative runs, so their workspace costs are not added together.
// The budget covers the larger branch while retaining the condition's storage.
fn branches(condition: bool)
    mem_peak <= mem_size(condition) + mem_size([u32; 64]),
{
    if condition {
        let scratch = [0u32; 64];
    } else {
        let scratch = [0u32; 32];
    }
}

// Shows why repeating work need not increase peak memory use.
//
// Workspace whose lifetime ends with an iteration can be reused by the next.
// This minimal example runs at most once, but exercises that accounting rule.
// Termination is a separate obligation, established by the decreasing expression.
// The condition remains live while each iteration uses its workspace.
fn reusable_loop(mut condition: bool)
    mem_peak <= mem_size(condition) + mem_size([u32; 64]),
{
    while condition
        decreases if condition { 1int } else { 0int },
    {
        let scratch = [0u32; 64];
        condition = false;
    }
}

// Shows that a detailed correctness proof need not increase runtime memory use.
//
// Ghost and proof data are erased, so even these deliberately large proof-only
// arrays leave the executable workspace's budget unchanged.
fn erased_proof_data()
    mem_peak <= mem_size([u32; 64]),
{
    let ghost large = [0u32; 4096usize];
    proof { let another = [0u32; 8192usize]; }
    let scratch = [0u32; 64];
}

// Keeps the demonstrations independently verifiable.
//
// Verus checks their contracts without requiring a runtime driver to call them.
fn main() {}

}
