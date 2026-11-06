// Shows how to check memory limits at individual stages of an operation.
//
// Checkpoints measure the highest modelled usage so far. Finishing a stage
// releases its workspace, but does not erase the peak it already reached.

use vstd::prelude::*;

verus! {

// Edits a separate copy while checking the memory needed along the way.
//
// The whole-function contract allows both arrays. The checkpoints show when
// that allowance becomes necessary and why the peak remains after scope exit.
fn main()
    peakmem <= 2 * sizeof([u32; 4]),
{
    let original = [1u32, 2, 3, 4];
    assert(peakmem <= sizeof(original));

    {
        let mut copy = original;
        copy[0] = 9;
        assert(peakmem <= sizeof(original) + sizeof(copy));
        assert(copy[0] == 9);
    }

    // The copy's storage has been released, but the earlier peak still counts.
    assert(peakmem <= 2 * sizeof(original));
    assert(original[0] == 1);
}

}
