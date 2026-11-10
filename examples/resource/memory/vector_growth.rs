// Grow a vector while proving that its memory use stays within budget.

use vstd::prelude::*;

verus! {

// Build the requested number of values within a growing memory allowance.
fn build(n: usize)
    requires n <= 8,
    resources memory <= 64 + 16 * n,
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
// The caller accounts for existing storage; the helper allows for growth.
fn append_to_empty(values: &mut Vec<u32>)
    requires old(values).len() == 0,
    ensures final(values).len() == 1 && final(values)[0] == 7,
    resources memory <= 24,
{
    values.push(7);
}

// Continue adding values after a helper has grown the vector.
fn use_helper()
    resources memory <= 64,
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
