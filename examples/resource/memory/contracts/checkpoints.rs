// This example shows how to distinguish memory still live from the peak reached
// earlier.
//
// While the copy exists, the peak includes two arrays. After its scope ends, only the
// original remains live, and the peak still includes both.

use vstd::prelude::*;

verus! {

/// `main` checks the current and peak charges before and after a working copy goes out
/// of scope.
///
/// The whole-function contract allows both arrays. The checkpoints show when
/// that allowance becomes necessary and why the peak remains after scope exit.
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
