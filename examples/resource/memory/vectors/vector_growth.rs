// This example shows how to bound a growing vector by the number of elements the
// program pushes.
//
// Each occupied slot contributes the size of a `u32`. A helper that appends through a
// borrow can account for the additional slot in its own contract.

use vstd::prelude::*;

verus! {

/// `build` pushes the requested number of values under one slot's allowance per value.
fn build(n: usize)
    requires n <= 8,
    resources peak(memory) <= value_size(n) + value_size(Vec<u32>)
        + n * value_size(u32),
{
    let mut values = Vec::<u32>::new();
    while values.len() < n
        invariant values.len() <= n, n <= 8,
        decreases n - values.len(),
    {
        values.push(7);
    }
    assert(values.len() == n);
}

/// `append_to_empty` grows an empty borrowed vector by one slot.
///
/// The caller accounts for existing storage; the helper allows for its reference
/// and one additional u32 slot.
fn append_to_empty(values: &mut Vec<u32>)
    requires old(values).len() == 0,
    ensures final(values).len() == 1 && final(values)[0] == 7,
    resources peak(memory) <= ref_size(values) + value_size(u32),
{
    values.push(7);
}

/// `use_helper` keeps the vector live across a helper push and a subsequent local push.
///
/// The helper call is the peak while the vector handle is live.
fn use_helper()
    resources peak(memory) <= value_size(Vec<u32>) + peak(append_to_empty),
{
    let mut values = Vec::<u32>::new();
    append_to_empty(&mut values);
    values.push(8);
    assert(values.len() == 2 && values[0] == 7 && values[1] == 8);
}

/// `main` runs the counted loop and the borrowed-vector example.
fn main() {
    build(8);
    use_helper();
}

}
