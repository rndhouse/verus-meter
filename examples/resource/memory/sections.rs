// Nested workspace budgets let a larger operation be checked in smaller pieces.
//
// Each section accounts for its own storage and the budgets of its children.
// The enclosing section or function remains responsible for storage already live
// when a child begins. peak(memory) always refers to the nearest section.

use vstd::prelude::*;

verus! {

// Keep an original array intact while using two layers of temporary workspace.
//
// The function owns the original; the outer section owns a working copy; the
// inner section owns scratch space. Each parent includes its child's allowance.
fn main()
    resources peak(memory) <= 3 * mem_size([u32; 4]),
{
    let original = [1u32, 2, 3, 4];

    resources peak(memory) <= 2 * mem_size(original) {
        // The original belongs to the function, so this section starts at zero.
        assert(peak(memory) <= 0);
        let mut copy = original;

        resources peak(memory) <= mem_size(copy) {
            // Both existing arrays belong to enclosing scopes.
            assert(peak(memory) <= 0);
            let scratch = copy;
            copy[0] = scratch[3];
            assert(peak(memory) <= mem_size(scratch));
        }

        // Scratch has gone out of scope, but its allowance remains in the peak.
        assert(peak(memory) <= 2 * mem_size(copy));
        assert(copy[0] == 4);
    }

    // Outside the sections, the checkpoint includes the original as well.
    assert(peak(memory) <= 3 * mem_size(original));
    assert(original[0] == 1);
}

}
