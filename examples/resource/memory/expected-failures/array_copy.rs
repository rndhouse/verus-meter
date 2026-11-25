// rust_verify/tests/example.rs expect-errors --- Intentionally exceeds its memory budget.
// This example shows how Verus Meter catches a copy that exceeds a one-array bound.
//
// Editing the copy leaves the original intact. Both need storage when the copy is
// created.

use vstd::prelude::*;

verus! {

/// `main` keeps an original array and edits a copy under a one-array contract.
///
/// Copying the array gives it separate storage. The assertions illustrate why
/// both arrays matter: changing the copy leaves the original untouched.
fn main()
    // Deliberately too small: this contract covers only one array.
    resources peak(memory) <= value_size([u32; 4]),
{
    let original = [1u32, 2, 3, 4];

    // Verus reports the violation here: the copy needs a second array's storage.
    let mut copy = original;
    copy[0] = 9;

    assert(original[0] == 1);
    assert(copy[0] == 9);
}

}
