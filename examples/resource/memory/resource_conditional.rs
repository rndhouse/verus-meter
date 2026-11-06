// An operation can promise different memory bounds for different inputs.
//
// Verus proves that each branch fits the allowance selected by the input.
// The storage charges still come from the memory model; the proof connects
// those charges to the condition in the contract.

use vstd::prelude::*;

verus! {

// Give a larger task more workspace while keeping the small task's promise tight.
//
// The input's own storage is needed in both cases. Only the selected branch's
// workspace must fit its allowance. Increasing either array beyond that
// allowance makes verification fail at its declaration.
fn workspace(large: bool)
    peakmem <= sizeof(large)
        + if large { sizeof([u32; 8]) } else { sizeof([u32; 4]) },
{
    if large {
        let scratch = [0u32; 8];
    } else {
        let scratch = [0u32; 4];
    }
}

// Reserve enough room to run either kind of task.
//
// For this first implementation, callers and peakmem(function) use the largest
// declared allowance. Consecutive calls reuse that workspace.
fn main()
    peakmem <= peakmem(workspace),
{
    workspace(false);
    workspace(true);
}

}
