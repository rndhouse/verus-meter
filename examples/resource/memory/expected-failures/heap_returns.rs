// rust_verify/tests/example.rs expect-errors --- Intentionally retains too many heap allocations.
// This example shows how Verus Meter catches a second allocation that overlaps a
// returned buffer.
//
// The caller budgets for two handles and one payload. The first payload is still live
// when it requests the second.

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
    resources peak(memory) <= 2 * value_size(Buffer) + value_size([u32; 4]),
{
    let first = make_buffer();

    // Verus rejects this call: the first allocation is still live when the
    // factory needs space for the second. Transferring ownership did not free it.
    let second = make_buffer();
}

}
