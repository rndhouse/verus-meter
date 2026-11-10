// Produce a buffer in a helper while keeping one allowance for the returned data.
//
// The caller can receive the buffer within the helper's allowance, without
// needing room for an additional copy.

use vstd::prelude::*;

verus! {

type Buffer = [u32; 4];

// Provide a ready-to-use buffer with a predictable memory requirement.
//
// Callers can rely on both the buffer's initial contents and its memory bound.
fn make_buffer() -> (buffer: Buffer)
    ensures buffer[0] == 7,
    resources peak(memory) <= owned_size(Buffer),
{
    [7u32; 4]
}

// Receive and use the buffer within the producer's declared allowance.
//
// Receiving the buffer preserves the producer's memory guarantee.
fn main()
    resources peak(memory) <= peak(make_buffer),
{
    let buffer = make_buffer();
    assert(buffer[0] == 7);
    assert(peak(memory) <= owned_size(Buffer));
}

}
