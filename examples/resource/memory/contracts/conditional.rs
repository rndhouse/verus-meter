// An operation can promise different memory bounds for different inputs.
//
// Verus proves that each branch fits the allowance selected by the input.
// Small tasks keep their smaller allowance even though the function also
// supports larger tasks.

use vstd::prelude::*;

verus! {

// Give a larger task more workspace while keeping the small task's promise tight.
//
// The input's own storage is needed in both cases. Only the selected branch's
// workspace must fit its allowance. Increasing either array beyond that
// allowance makes verification fail at its declaration.
fn workspace(large: bool)
    resources peak(memory) <= value_size(large)
        + if large { value_size([u32; 8]) } else { value_size([u32; 4]) },
{
    if large {
        let scratch = [0u32; 8];
    } else {
        let scratch = [0u32; 4];
    }
}

// Reserve enough room to run either kind of task.
//
// The argument-free query allows either input. Each actual call uses the
// allowance selected by its argument; consecutive calls reuse that workspace.
fn main()
    resources peak(memory) <= peak(workspace),
{
    workspace(false);
    workspace(true);
}

}
