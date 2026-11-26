// This example shows how to follow a vector's storage when it becomes a boxed slice.
//
// The vector reserves four slots and fills two. The returned slice owns two elements
// until its final owner drops it.

use vstd::prelude::*;

verus! {

type FinalScratch = [u8; 96];

/// `pack` returns two values in a boxed slice after reserving four vector slots.
///
/// The input reservation determines the backing peak. The returned slice
/// retains only its two elements.
fn pack() -> (b: Box<[u32]>)
    ensures b.len() == 2, b[0] == 7, b[1] == 9,
    resources peak(memory) <=
        value_size(Vec<u32>)       // The vector header before conversion.
        + value_size(Box<[u32]>)   // The boxed slice handle returned by pack.
        + value_size([u32; 4]),    // Four slots were reserved, even though only two are filled.
{
    let mut v = Vec::<u32>::with_capacity(4);
    v.push(7);
    v.push(9);
    v.into_boxed_slice()
}

/// `forward` transfers the boxed slice to its next owner.
fn forward(b: Box<[u32]>) -> (r: Box<[u32]>)
    ensures r == b,
    resources peak(memory) <= value_size(Box<[u32]>),
{
    b
}

/// `main` releases the returned slice before using the allowance for scratch.
///
/// The later byte workspace sets the allowance for the complete operation.
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
