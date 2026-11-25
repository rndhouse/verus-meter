// This example shows how nested memory contracts account for an original array, a copy,
// and scratch.
//
// Each section checks the workspace it introduces. The enclosing function counts all
// three arrays when their lifetimes overlap.

use vstd::prelude::*;

verus! {

/// `main` checks each section's peak as the copy and scratch enter and leave scope.
///
/// The function owns the original; the outer section owns a working copy; the
/// inner section owns scratch space. Each parent includes its child's allowance.
fn main()
    resources peak(memory) <= 3 * value_size([u32; 4]),
{
    let original = [1u32, 2, 3, 4];

    resources peak(memory) <= 2 * value_size(original) {
        // The original belongs to the function, so this section starts at zero.
        assert(peak(memory) <= 0);
        let mut copy = original;

        resources peak(memory) <= value_size(copy) {
            // Both existing arrays belong to enclosing scopes.
            assert(peak(memory) <= 0);
            let scratch = copy;
            copy[0] = scratch[3];
            assert(peak(memory) <= value_size(scratch));
        }

        // Scratch has gone out of scope, but its allowance remains in the peak.
        assert(peak(memory) <= 2 * value_size(copy));
        assert(copy[0] == 4);
    }

    // Outside the sections, the checkpoint includes the original as well.
    assert(peak(memory) <= 3 * value_size(original));
    assert(original[0] == 1);
}

}
