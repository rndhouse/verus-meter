// Give a reusable name to a memory bound that grows with the input.
//
// Verus reasons about the formula symbolically and checks it for every capacity
// allowed by the precondition. Specification functions add no runtime work.

use vstd::prelude::*;

verus! {

// Describe the reservation for a collection of u32 values.
//
// Each element needs four bytes in the source memory model. The formula uses
// mathematical naturals; the memory contract separately checks the u64 limit.
spec fn element_bytes(capacity: nat) -> nat {
    4 * capacity
}

// Collect values within a reservation chosen by the caller.
//
// The named formula covers the elements; the contract also covers the capacity
// parameter and vector handle. The precondition bounds every permitted input.
fn collect(capacity: usize)
    requires 2 <= capacity <= 1024,
    mem_peak <= mem_size(capacity) + mem_size(Vec<u32>)
        + element_bytes(capacity as nat),
{
    let mut values = Vec::<u32>::with_capacity(capacity);
    values.push(10);
    values.push(20);
    assert(values[0] == 10 && values[1] == 20);
}

// Carry the helper's input-specific guarantee through to the complete operation.
fn main()
    mem_peak <= mem_peak(collect(2)),
{
    collect(2);
}

}
