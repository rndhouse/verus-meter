// rust_verify/tests/example.rs expect-errors --- Intentionally exceeds its memory budget.
// Keeping two heap buffers alive requires space for both allocations.
//
// The contract allows two owning handles but only one heap buffer. Both handles
// remain in scope, so their allocations cannot share that allowance.

use vstd::prelude::*;

verus! {

type Buffer = [u8; 16];

// Try to preserve one buffer while creating another under a one-buffer allowance.
//
// Ending the first owner's scope or explicitly dropping it would release its
// heap object. This example deliberately keeps it alive to expose the violation.
fn main()
    mem_peak <= 2 * mem_size(Box<Buffer>) + mem_size(Buffer),
{
    let first = Box::new([0u8; 16]);

    // Verus reports the violation at this allocation: the first heap object is
    // still live, and the declared allowance cannot hold a second one.
    let second = Box::new([0u8; 16]);
}

}
