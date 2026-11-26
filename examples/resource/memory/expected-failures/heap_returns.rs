// rust_verify/tests/example.rs expect-errors --- Intentionally retains too many heap allocations.
// This example shows how Verus Meter catches a second allocation that overlaps a
// returned buffer.
//
// The caller budgets for two handles and one payload. The first payload is still live
// when it requests the second.
//
// Look for the two `FAIL:` comments at the one-payload bound and the second call.

use vstd::prelude::*;

verus! {

type Buffer = Box<[u32; 4]>;

/// `make_buffer` returns a fresh box containing a four-element array.
fn make_buffer() -> Buffer
    resources peak(memory) <= value_size(Buffer) + value_size([u32; 4]),
{
    Box::new([0u32; 4])
}

/// `main` retains the first returned box while requesting another under a one-payload
/// bound.
fn main()
    // FAIL: The bound counts two box handles but only one four-element array.
    resources peak(memory) <= 2 * value_size(Buffer) + value_size([u32; 4]),
{
    let first = make_buffer();

    // FAIL: This call allocates a second array while first still owns its array.
    let second = make_buffer();
}

}
