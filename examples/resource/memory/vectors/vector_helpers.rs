// Share a reserved buffer between helpers while keeping its memory use bounded.
//
// The caller supplies room for the additions; the helpers use the same allocation.

use vstd::prelude::*;

verus! {

// Add a value when the caller has reserved enough room for it.
fn append(values: &mut Vec<u32>, capacity: usize, value: u32)
    requires
        old(values).len() < capacity,
    ensures
        final(values)@ == old(values)@.push(value),
    resources peak(memory) <= ref_size(values) + value_size(capacity) + value_size(value),
{
    values.push(value);
}

// Report the result without copying or taking ownership of the collection.
fn count(values: &Vec<u32>) -> (n: usize)
    ensures
        n == values.len(),
    resources peak(memory) <= ref_size(values) + value_size(usize),
{
    values.len()
}

// Combine helper guarantees to fill and inspect a bounded collection.
//
// The caller reserves space for two elements; helpers add their declared needs.
fn build()
    resources peak(memory) <= value_size(Vec<u32>) + 2 * value_size(u32) + peak(append),
{
    let mut values = Vec::<u32>::with_capacity(2);
    append(&mut values, 2, 10);
    append(&mut values, 2, 20);
    let n = count(&values);
    assert(n == 2 && values[0] == 10 && values[1] == 20);
}

// Run the complete operation.
fn main() { build(); }

}
