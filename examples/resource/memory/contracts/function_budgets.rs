// Build a reusable memory formula for collections of different element sizes.
//
// Fix the element size once, then reuse the formula for different capacities.

use vstd::prelude::*;

verus! {

// Describe a family of reservations using one captured element size.
spec fn reservation(bytes_per_item: nat) -> spec_fn(nat) -> nat {
    |capacity: nat| value_size(Vec<u32>) + bytes_per_item * capacity
}

// Collect values within a reservation chosen by the caller.
//
// The formula covers the vector handle and reserved elements. The contract
// also counts the capacity parameter; the precondition bounds every input.
fn collect(capacity: usize)
    requires 2 <= capacity <= 1024,
    resources peak(memory) <= value_size(capacity) + reservation(value_size(u32))(capacity as nat),
{
    let mut values = Vec::<u32>::with_capacity(capacity);
    values.push(10);
    values.push(20);
    assert(values[0] == 10 && values[1] == 20);
}

// Carry the helper's input-specific guarantee through to the complete operation.
fn main()
    resources peak(memory) <= peak(collect(2)),
{
    collect(2);
}

}
