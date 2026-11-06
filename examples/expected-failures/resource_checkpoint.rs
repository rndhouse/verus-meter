// rust_verify/tests/example.rs expect-errors --- Intentionally fails a memory checkpoint.
// Shows a checkpoint catching a copy that exceeds a stage's memory allowance.
//
// The whole-function contract has room for both arrays. The checkpoint asks
// for a tighter bound at this particular point, and Verus must reject it.

use vstd::prelude::*;

verus! {

// Preserves an original array while making a copy that breaks the checkpoint.
//
// The error belongs to the assertion: copying is permitted by the function's
// contract, but the claimed peak at this point only allows one array.
fn main()
    peakmem <= 2 * sizeof([u32; 4]),
{
    let original = [1u32, 2, 3, 4];
    let copy = original;

    // Verus reports the violation here: the peak includes both arrays.
    assert(current(peakmem) <= sizeof(original));
    assert(copy[0] == original[0]);
}

}
