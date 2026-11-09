// Inline handles and separately allocated storage compose through fixed owners.
// Dropping the outer box releases the struct and both of its owned allocations.
use vstd::prelude::*;

verus! {

struct Buffer {
    values: Vec<u32>,
    marker: Box<u32>,
}

fn make(n: usize) -> (b: Box<Buffer>)
    requires n <= 4,
    ensures b.values.len() == 0, *b.marker == 42,
    mem_peak <= 52 + 4 * n,
{
    Box::new(Buffer { values: Vec::with_capacity(n), marker: Box::new(42) })
}

fn forward(b: Box<Buffer>) -> (r: Box<Buffer>)
    ensures r == b,
    mem_peak <= 8,
{
    b
}

fn main()
    mem_peak <= 96,
{
    let first = make(4);
    let second = forward(first);
    let length = second.values.len();
    assert(length == 0);
    assert(*second.marker == 42);
    drop(second);
    let scratch = [0u8; 88];
}

}
