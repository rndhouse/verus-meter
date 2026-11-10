// Shows how to check memory limits at individual stages of an operation.
//
// Compare memory still in use with the highest usage reached so far. Finishing
// a stage releases its workspace, but does not erase its earlier peak.

use vstd::prelude::*;

verus! {

// Edits a separate copy while checking the memory needed along the way.
//
// The whole-function contract allows both arrays. The checkpoints show when
// that allowance becomes necessary and why the peak remains after scope exit.
fn main()
    resources peak(memory) <= 2 * value_size([u32; 4]),
{
    let original = [1u32, 2, 3, 4];
    assert(peak(memory) <= value_size(original));

    {
        let mut copy = original;
        copy[0] = 9;
        assert(peak(memory) <= value_size(original) + value_size(copy));
        assert(copy[0] == 9);
    }

    // Only the original remains live; the earlier peak still includes the copy.
    assert(current(memory) <= value_size(original));
    assert(peak(memory) <= 2 * value_size(original));
    assert(original[0] == 1);
}

}
