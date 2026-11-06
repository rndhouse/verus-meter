// A small task can keep its memory allowance small across a chain of helpers.
//
// Each caller refers to the next helper's contract with the arguments it will
// receive. The allowance follows those arguments through the whole chain.

use vstd::prelude::*;

verus! {

// Give each kind of task enough workspace without overpromising for small tasks.
//
// The function must prove both cases of its promise. Increasing an array beyond
// its selected allowance causes verification to fail at that declaration.
fn workspace(large: bool)
    mem_peak <= mem_size(large)
        + if large { mem_size([u32; 8]) } else { mem_size([u32; 4]) },
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
    mem_peak <= mem_size(large) + mem_peak(workspace(large)),
{
    workspace(large);
}

// Run a small task under an allowance that would reject a large task.
//
// Changing the argument in the executable call below to true makes verification
// fail at that call: the declared budget still allows only the small task.
fn main()
    mem_peak <= mem_peak(delegate(false)),
{
    delegate(false);
    assert(current(mem_peak) <= mem_peak(delegate(false)));
}

}
