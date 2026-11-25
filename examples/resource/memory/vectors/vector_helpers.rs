// This example shows how several helpers can share a single two-element reservation.
//
// The caller reserves the slots once. Each append borrows the vector, and the final
// helper reads its length.

use vstd::prelude::*;

verus! {

/// `append` appends a value while the logical length is below the supplied capacity.
fn append(values: &mut Vec<u32>, capacity: usize, value: u32)
    requires
        old(values).len() < capacity,
    ensures
        final(values)@ == old(values)@.push(value),
    resources peak(memory) <= ref_size(values) + value_size(capacity) + value_size(value),
{
    values.push(value);
}

/// `count` reads the vector's length through a shared borrow.
fn count(values: &Vec<u32>) -> (n: usize)
    ensures
        n == values.len(),
    resources peak(memory) <= ref_size(values) + value_size(usize),
{
    values.len()
}

/// `build` reserves two slots and fills them through successive helper calls.
///
/// The two append calls run in sequence, so the caller needs the helper's workspace once.
fn build()
    resources peak(memory) <= value_size(Vec<u32>) + 2 * value_size(u32) + peak(append),
{
    let mut values = Vec::<u32>::with_capacity(2);
    append(&mut values, 2, 10);
    append(&mut values, 2, 20);
    let n = count(&values);
    assert(n == 2 && values[0] == 10 && values[1] == 20);
}

/// `main` runs the two-slot collection example.
fn main() { build(); }

}
