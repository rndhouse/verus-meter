// rust_verify/tests/example.rs expect-errors --- Intentionally retains too many heap allocations.
// Returned heap buffers keep using memory until their owners release them.
//
// The budget allows two handles but only one allocation. Calling the factory
// again while retaining the first buffer makes the allocations overlap.

use vstd::prelude::*;

verus! {

type Buffer = Box<[u32; 4]>;

// Supply one independently owned buffer.
fn make_buffer() -> Buffer
    resources mem_peak <= mem_size(Buffer) + mem_size([u32; 4]),
{
    Box::new([0u32; 4])
}

// Try to keep two heap buffers under a one-allocation allowance.
fn main()
    resources mem_peak <= 2 * mem_size(Buffer) + mem_size([u32; 4]),
{
    let first = make_buffer();

    // Verus rejects this call: the first allocation is still live when the
    // factory needs space for the second. Transferring ownership did not free it.
    let second = make_buffer();
}

}
