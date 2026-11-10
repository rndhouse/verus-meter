// Collect selected numbers while keeping the result within a reserved memory allowance.
//
// The capacity comes from the caller. The memory contract scales with it, and
// each push must be proved to fit without growing the vector.

use vstd::prelude::*;

verus! {

// Describe the memory needed to filter numbers at the chosen capacity.
//
// The budget covers the input, reserved result, and values tracking progress.
spec fn collection_budget(capacity: nat) -> nat {
    owned_size(usize) + owned_size(Vec<u32>) + capacity * owned_size(u32)
        + owned_size([u32; 4]) + owned_size(usize)
}

// Keep the positive numbers from a small input without growing the result buffer.
//
// Reserving enough room for the whole input also covers any selection from it.
// The loop relates the number collected to the number examined, giving Verus
// the evidence it needs to check every push.
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

// Give the collection task exactly the allowance promised for this capacity.
//
// The call query substitutes the argument into the helper's memory formula.
fn main()
    resources peak(memory) <= peak(collect_positive(4)),
{
    collect_positive(4);
}

}
