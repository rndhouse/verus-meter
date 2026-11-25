// This example shows how to specialize a memory formula by element size and then apply
// it to different capacities.
//
// The collector uses the size of a `u32` to turn its requested slot count into a byte
// allowance.

use vstd::prelude::*;

verus! {

/// `reservation` returns a formula for the vector header and a chosen number of slots.
spec fn reservation(bytes_per_item: nat) -> spec_fn(nat) -> nat {
    |capacity: nat| value_size(Vec<u32>) + bytes_per_item * capacity
}

/// `collect` reserves the requested number of slots and uses two of them.
///
/// The formula covers the vector handle and reserved elements. The contract
/// also counts the capacity parameter; the precondition bounds every input.
fn collect(capacity: usize)
    requires 2 <= capacity <= 1024,
    resources peak(memory) <= value_size(capacity) + reservation(value_size(u32))(capacity as nat),
{
    let mut values = Vec::<u32>::with_capacity(capacity);
    values.push(10);
    values.push(20);
    assert(values[0] == 10 && values[1] == 20);
}

/// `main` runs the collector with an allowance specialized to two slots.
fn main()
    resources peak(memory) <= peak(collect(2)),
{
    collect(2);
}

}
