// This example shows how to prove that filtering an array fits a vector's initial
// reservation.
//
// Each input contributes at most one output. The loop tracks how many inputs it has
// examined, so every push fits the caller's chosen capacity.

use vstd::prelude::*;

verus! {

/// `collection_budget` counts the reserved result, the input array, and the scalar
/// state used during filtering.
spec fn collection_budget(capacity: nat) -> nat {
    // The two usize slots hold the capacity input and the loop index. The input array
    // stays live alongside the result vector and its explicitly reserved slots.
    value_size(usize) + value_size(Vec<u32>) + capacity * value_size(u32)
        + value_size([u32; 4]) + value_size(usize)
}

/// `collect_positive` collects positive values under a bound that scales with the
/// reserved capacity.
///
/// Reserving enough room for the whole input also covers any selection from it.
/// The loop relates the number collected to the number examined, giving Verus
/// the evidence it needs to check every push.
fn collect_positive(capacity: usize)
    requires 4 <= capacity <= 16,
    resources peak(memory) <= collection_budget(capacity as nat),
{
    let input = [0u32, 4, 0, 7];
    let mut selected = Vec::<u32>::with_capacity(capacity);
    let mut i: usize = 0;
    while i < 4
        invariant
            i <= 4,
            4 <= capacity <= 16,
            selected.len() <= i,
            forall|k: int| 0 <= k < selected.len() ==> selected[k] > 0,
        decreases 4 - i,
    {
        if input[i] > 0 {
            selected.push(input[i]);
        }
        i = i + 1;
    }
    assert(selected.len() <= capacity);
}

/// `main` runs the filter with one reserved slot per input.
///
/// The call query substitutes the argument into the helper's memory formula.
fn main()
    resources peak(memory) <= peak(collect_positive(4)),
{
    collect_positive(4);
}

}
