// This example shows how a small task keeps its smaller memory bound through two layers
// of calls.
//
// Each caller queries the next helper's declared peak with the argument it will pass.
// The small task therefore pays for the smaller scratch array throughout.

use vstd::prelude::*;

verus! {

/// `scratch_budget` selects the scratch array size for the requested task.
spec fn scratch_budget(large: bool) -> nat {
    if large {
        value_size([u32; 8])
    } else {
        value_size([u32; 4])
    }
}

/// `workspace` uses the array covered by the selected scratch allowance.
///
/// The function must prove both cases of its promise. Increasing an array beyond
/// its selected allowance causes verification to fail at that declaration.
/// The callers compose this named formula through the helper contracts.
fn workspace(large: bool)
    resources peak(memory) <= value_size(large) + scratch_budget(large),
{
    if large {
        let scratch = [0u32; 8];
    } else {
        let scratch = [0u32; 4];
    }
}

/// `delegate` includes its own live flag alongside the helper's allowance for that
/// flag.
///
/// The query reads workspace's declared allowance for this input; it does not
/// execute workspace. This function also needs room for its own live input.
fn delegate(large: bool)
    resources peak(memory) <= value_size(large) + peak(workspace(large)),
{
    workspace(large);
}

/// `main` runs the small task and checks a peak of two flags and one small array.
///
/// Changing the argument in the executable call below to true makes verification
/// fail: the declared budget still allows only the small task.
fn main()
    resources peak(memory) <= peak(delegate(false)),
{
    delegate(false);
    // Checkpoints need a fixed bound: two flags and the small task's array.
    assert(peak(memory) <= 2 * value_size(bool) + value_size([u32; 4]));
}

}
