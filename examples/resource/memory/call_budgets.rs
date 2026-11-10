// A small task can keep its memory allowance small across a chain of helpers.
//
// Each caller refers to the next helper's contract with the arguments it will
// receive. The allowance follows those arguments through the whole chain.

use vstd::prelude::*;

verus! {

// Give each task a reusable allowance for its temporary data.
spec fn scratch_budget(large: bool) -> nat {
    if large {
        mem_size([u32; 8])
    } else {
        mem_size([u32; 4])
    }
}

// Give each kind of task enough workspace without overpromising for small tasks.
//
// The function must prove both cases of its promise. Increasing an array beyond
// its selected allowance causes verification to fail at that declaration.
// The callers compose this named formula through the helper contracts.
fn workspace(large: bool)
    resources mem_peak <= mem_size(large) + scratch_budget(large),
{
    if large {
        let scratch = [0u32; 8];
    } else {
        let scratch = [0u32; 4];
    }
}

// Preserve the task's memory promise when delegating its work.
//
// The query reads workspace's declared allowance for this input; it does not
// execute workspace. This function also needs room for its own live input.
fn delegate(large: bool)
    resources mem_peak <= mem_size(large) + mem_peak(workspace(large)),
{
    workspace(large);
}

// Run a small task under an allowance that would reject a large task.
//
// Changing the argument in the executable call below to true makes verification
// fail: the declared budget still allows only the small task.
fn main()
    resources mem_peak <= mem_peak(delegate(false)),
{
    delegate(false);
    // Checkpoints need a fixed bound: two flags and the small task's array.
    assert(current(mem_peak) <= 2 * mem_size(bool) + mem_size([u32; 4]));
}

}
