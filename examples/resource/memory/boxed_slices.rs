// Convert spare vector capacity into a fixed-length owning slice.
// The model budgets both buffers during conversion, then retains only the slice.
use vstd::prelude::*;

verus! {

fn pack() -> (b: Box<[u32]>)
    ensures b.len() == 2, b[0] == 7, b[1] == 9,
    mem_peak <= 64,
{
    let mut v = Vec::<u32>::with_capacity(4);
    v.push(7);
    v.push(9);
    v.into_boxed_slice()
}

fn forward(b: Box<[u32]>) -> (r: Box<[u32]>)
    ensures r == b,
    mem_peak <= mem_size(Box<[u32]>),
{
    b
}

fn main()
    mem_peak <= 96,
{
    // A local runtime extent is exported conservatively using pack's budget.
    let b = pack();
    let c = forward(b);
    assert(c[0] == 7);
    drop(c);
    let scratch = [0u8; 96];
}

}
