// This example shows how to name the part of a vector's memory bound that grows with
// capacity.
//
// The collector adds its fixed storage to the same element-size formula for every
// permitted input.

use vstd::prelude::*;

verus! {

/// `element_bytes` converts a count of reserved `u32` elements to bytes.
///
/// Keeping this formula separate lets other operations reuse the same allowance.
spec fn element_bytes(capacity: nat) -> nat {
    value_size(u32) * capacity
}

/// `collect` reserves the requested number of slots and fills two.
///
/// The named formula covers the elements; the contract also covers the capacity
/// parameter and vector handle. The precondition bounds every permitted input.
fn collect(capacity: usize)
    requires 2 <= capacity <= 1024,
    resources peak(memory) <= value_size(capacity) + value_size(Vec<u32>)
        + element_bytes(capacity as nat),
{
    let mut values = Vec::<u32>::with_capacity(capacity);
    values.push(10);
    values.push(20);
    assert(values[0] == 10 && values[1] == 20);
}

/// `main` checks the collector with the bound for two slots.
fn main()
    resources peak(memory) <= peak(collect(2)),
{
    collect(2);
}

}
