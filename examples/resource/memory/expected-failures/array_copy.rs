// rust_verify/tests/example.rs expect-errors --- Intentionally exceeds its memory budget.
// Shows that keeping an independent copy requires room for both arrays.
//
// The budget allows one array, but the original and its copy coexist.
// Verification rejects the extra copy because both arrays need room at once.

use vstd::prelude::*;

verus! {

// Tries to edit a copy while preserving the original, with room for only one.
//
// Copying the array gives it separate storage. The assertions illustrate why
// both arrays matter: changing the copy leaves the original untouched.
fn main()
    // Deliberately too small: this contract covers only one array.
    resources mem_peak <= mem_size([u32; 4]),
{
    let original = [1u32, 2, 3, 4];

    // Verus reports the violation here: the copy needs a second array's storage.
    let mut copy = original;
    copy[0] = 9;

    assert(original[0] == 1);
    assert(copy[0] == 9);
}

}
