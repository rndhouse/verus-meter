// Grow a vector while proving that its memory use stays within budget.
//
use vstd::prelude::*;

verus! {

// Build the requested number of values within a growing memory allowance.
//
// Each value occupies one u32 slot.
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

// Let a helper grow a borrowed vector within a checked allowance.
//
// The caller accounts for existing storage; the helper allows for its reference
// and one additional u32 slot.
fn append_to_empty(values: &mut Vec<u32>)
    requires old(values).len() == 0,
    ensures final(values).len() == 1 && final(values)[0] == 7,
    resources peak(memory) <= ref_size(values) + value_size(u32),
{
    values.push(7);
}

// Continue adding values after a helper has grown the vector.
//
// The helper call is the peak while the vector handle is live.
fn use_helper()
    resources peak(memory) <= value_size(Vec<u32>) + peak(append_to_empty),
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
