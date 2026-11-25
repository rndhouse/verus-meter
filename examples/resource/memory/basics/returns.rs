// This example shows how to return an array within a single array's memory allowance.
//
// The caller receives the array built by the helper and can use its peak bound for the
// whole operation.

use vstd::prelude::*;

verus! {

type Buffer = [u32; 4];

/// `make_buffer` returns an initialized array within the allowance for one buffer.
///
/// Callers can rely on both the buffer's initial contents and its memory bound.
fn make_buffer() -> (buffer: Buffer)
    ensures buffer[0] == 7,
    resources peak(memory) <= value_size(Buffer),
{
    [7u32; 4]
}

/// `main` checks the returned value and the peak after receiving it.
fn main()
    resources peak(memory) <= peak(make_buffer),
{
    let buffer = make_buffer();
    assert(buffer[0] == 7);
    assert(peak(memory) <= value_size(Buffer));
}

}
