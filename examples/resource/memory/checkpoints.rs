// Shows how to check memory limits at individual stages of an operation.
//
// Each checkpoint inspects the peak reached at its position. Finishing a stage
// releases its workspace, but does not erase the peak it already reached.

use vstd::prelude::*;

verus! {

// Edits a separate copy while checking the memory needed along the way.
//
// The whole-function contract allows both arrays. The checkpoints show when
// that allowance becomes necessary and why the peak remains after scope exit.
fn main()
    mem_peak <= 2 * mem_size([u32; 4]),
{
    let original = [1u32, 2, 3, 4];
    assert(current(mem_peak) <= mem_size(original));

    {
        let mut copy = original;
        copy[0] = 9;
        assert(current(mem_peak) <= mem_size(original) + mem_size(copy));
        assert(copy[0] == 9);
    }

    // The copy's storage has been released, but the earlier peak still counts.
    assert(current(mem_peak) <= 2 * mem_size(original));
    assert(original[0] == 1);
}

}
