// Grow a vector while proving that its memory use stays within budget.

use vstd::prelude::*;

verus! {

// Build the requested number of values within a growing memory allowance.
//
// The model's minimum u32 vector buffer holds four elements. Allow two such
// buffers of fixed headroom, plus another per requested value, to cover
// replacement overlap and conservative loop accounting.
fn build(n: usize)
    requires n <= 8,
    resources peak(memory) <= mem_size(n) + mem_size(Vec<u32>)
        + 2 * mem_size([u32; 4]) + n * mem_size([u32; 4]),
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

// Let a helper grow a borrowed vector within a checked allowance.
//
// The caller accounts for existing storage; the helper allows for its reference
// and one minimum four-element buffer.
fn append_to_empty(values: &mut Vec<u32>)
    requires old(values).len() == 0,
    ensures final(values).len() == 1 && final(values)[0] == 7,
    resources peak(memory) <= mem_size(values) + mem_size([u32; 4]),
{
    values.push(7);
}

// Continue adding values after a helper has grown the vector.
//
// Allow for the vector handle, the helper's budget, and another minimum buffer
// of growth headroom for subsequent work.
fn use_helper()
    resources peak(memory) <= mem_size(Vec<u32>) + mem_peak(append_to_empty) + mem_size([u32; 4]),
{
    let mut values = Vec::<u32>::new();
    append_to_empty(&mut values);
    values.push(8);
    assert(values.len() == 2 && values[0] == 7 && values[1] == 8);
}

// Run both growth examples.
fn main() {
    build(8);
    use_helper();
}

}
