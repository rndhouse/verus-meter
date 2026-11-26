// rust_verify/tests/example.rs expect-errors --- Intentionally fails a memory checkpoint.
// This example shows how a peak checkpoint can fail even when the function's budget is
// sufficient.
//
// The function allows two arrays. After copying the original, the checkpoint claims
// that only one array's worth of storage has been used.
//
// Look for the two `FAIL:` comments at the copy and the checkpoint that undercounts it.

use vstd::prelude::*;

verus! {

/// `main` copies an array and makes a peak claim that omits the copy.
///
/// The error belongs to the assertion: copying is permitted by the function's
/// contract, but the claimed peak at this point only allows one array.
fn main()
    resources peak(memory) <= 2 * value_size([u32; 4]),
{
    let original = [1u32, 2, 3, 4];
    // FAIL: Creating the copy brings the peak to two arrays.
    let copy = original;

    // FAIL: This checkpoint claims a peak of one array after both have been live.
    assert(peak(memory) <= value_size(original));
    assert(copy[0] == original[0]);
}

}
