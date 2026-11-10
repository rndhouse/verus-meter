// rust_verify/tests/example.rs expect-errors --- Intentionally keeps more returned data than allowed.
// Returned buffers keep consuming storage while their owners remain in scope.
//
// Each helper call fits on its own. Keeping both results requires an allowance
// for two buffers, even though the helper itself needs room for only one.

use vstd::prelude::*;

verus! {

type Buffer = [u32; 4];

// Provide one buffer within a one-buffer allowance.
//
// Its result becomes the caller's buffer without an extra copy.
fn make_buffer() -> Buffer
    resources peak(memory) <= owned_size(Buffer),
{
    [0u32; 4]
}

// Try to retain two independent results under a one-buffer allowance.
//
// The first result stays live when the second destination is introduced.
fn main()
    resources peak(memory) <= peak(make_buffer),
{
    let first = make_buffer();

    // Verus reports the violation here: the two returned buffers must coexist.
    let second = make_buffer();
}

}
