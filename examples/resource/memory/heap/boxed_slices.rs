// Turn a growable collection into a fixed-length buffer within a memory budget.

use vstd::prelude::*;

verus! {

type FinalScratch = [u8; 96];

// Produce a fixed-length buffer containing the selected values.
//
// The input reservation determines the backing peak. The returned slice
// retains only its two elements.
fn pack() -> (b: Box<[u32]>)
    ensures b.len() == 2, b[0] == 7, b[1] == 9,
    resources peak(memory) <= value_size(Vec<u32>) + value_size(Box<[u32]>)
        + value_size([u32; 4]),
{
    let mut v = Vec::<u32>::with_capacity(4);
    v.push(7);
    v.push(9);
    v.into_boxed_slice()
}

// Pass the buffer to another owner without creating a copy.
fn forward(b: Box<[u32]>) -> (r: Box<[u32]>)
    ensures r == b,
    resources peak(memory) <= value_size(Box<[u32]>),
{
    b
}

// Release the returned buffer before using the allowance for another task.
//
// The later byte workspace sets the allowance for the complete operation.
fn main()
    resources peak(memory) <= value_size(FinalScratch),
{
    let b = pack();
    let c = forward(b);
    assert(c[0] == 7);
    drop(c);
    let scratch: FinalScratch = [0; 96];
}

}
