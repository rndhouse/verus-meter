// rust_verify/tests/example.rs expect-errors --- Intentionally exceeds its memory budget.
// This example shows how Verus Meter catches a copy that exceeds a one-array bound.
//
// Editing the copy leaves the original intact. Both need storage when the copy is
// created.
//
// Look for the two `FAIL:` comments at the one-array bound and the copy that exceeds it.

use vstd::prelude::*;

verus! {

/// `main` keeps an original array and edits a copy under a one-array contract.
///
/// Copying the array gives it separate storage. The assertions illustrate why
/// both arrays matter: changing the copy leaves the original untouched.
fn main()
    // FAIL: This bound allows room for one array.
    resources peak(memory) <= value_size([u32; 4]),
{
    let original = [1u32, 2, 3, 4];

    // FAIL: The copy needs its own four slots while the original array is still live.
    let mut copy = original;
    copy[0] = 9;

    assert(original[0] == 1);
    assert(copy[0] == 9);
}

}
