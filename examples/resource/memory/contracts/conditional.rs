// This example shows how one function can promise a smaller memory bound for a smaller
// task.
//
// The input flag selects both the executable branch and its scratch allowance. A caller
// that accepts either input can use the larger bound.

use vstd::prelude::*;

verus! {

/// `workspace` chooses a scratch array and proves the corresponding input-specific
/// bound.
///
/// The input's own storage is needed in both cases. Only the selected branch's
/// workspace must fit its allowance. Increasing either array beyond that
/// allowance makes verification fail at its declaration.
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

/// `main` runs both task sizes in sequence within the larger allowance.
///
/// The argument-free query allows either input. Each actual call uses the
/// allowance selected by its argument; consecutive calls reuse that workspace.
fn main()
    resources peak(memory) <= peak(workspace),
{
    workspace(false);
    workspace(true);
}

}
