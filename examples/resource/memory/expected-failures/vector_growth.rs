// rust_verify/tests/example.rs expect-errors --- Intentionally requires unbudgeted growth.
// This example shows how Verus Meter catches a push that exceeds a one-element memory
// bound.
//
// The first value fits the explicit reservation. The second needs another occupied
// slot.

use vstd::prelude::*;

verus! {

/// `main` pushes two values under a budget for the vector and one slot.
///
/// The first push fits. The second needs additional backing storage that the
/// contract has not allowed for.
fn main()
    resources peak(memory) <= value_size(Vec<u32>) + value_size(u32),
{
    let mut values = Vec::<u32>::with_capacity(1);
    values.push(10);

    // The second occupied slot exceeds the memory budget at this push.
    values.push(20);
}

}
