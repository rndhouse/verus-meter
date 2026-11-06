// Produce a buffer in a helper while keeping one allowance for the returned data.
//
// The helper's budget includes its result. The caller's destination shares that
// charge, so handing over the buffer does not require another buffer allowance.

use vstd::prelude::*;

verus! {

type Buffer = [u32; 4];

// Provide a ready-to-use buffer with a predictable memory requirement.
//
// The array initializes the function's result directly. Its functional promise
// lets callers rely on the initial contents as well as the memory allowance.
fn make_buffer() -> (buffer: Buffer)
    ensures buffer[0] == 7,
    mem_peak <= mem_size(Buffer),
{
    [7u32; 4]
}

// Receive and use the buffer within the producer's declared allowance.
//
// The local becomes the result's destination; both contracts count it once.
fn main()
    mem_peak <= mem_peak(make_buffer),
{
    let buffer = make_buffer();
    assert(buffer[0] == 7);
    assert(current(mem_peak) <= mem_size(Buffer));
}

}
