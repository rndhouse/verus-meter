// Grow a vector while proving that its memory use stays within budget.

use vstd::prelude::*;

verus! {

fn build(n: usize)
    requires n <= 8,
    mem_peak <= 64 + 16 * n,
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

// The caller keeps paying for its input buffer during this call. The helper's
// budget includes its reference and a possible four-element replacement buffer.
fn append_to_empty(values: &mut Vec<u32>)
    requires old(values).len() == 0,
    ensures final(values).len() == 1 && final(values)[0] == 7,
    mem_peak <= 24,
{
    values.push(7);
}

fn use_helper()
    mem_peak <= 64,
{
    let mut values = Vec::<u32>::new();
    append_to_empty(&mut values);
    values.push(8);
    assert(values.len() == 2 && values[0] == 7 && values[1] == 8);
}

fn main() {
    build(8);
    use_helper();
}

}
