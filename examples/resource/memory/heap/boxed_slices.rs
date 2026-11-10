// Turn a growable collection into a fixed-length buffer within a memory budget.
//
// Conversion needs room for both buffers until the original is released.

use vstd::prelude::*;

verus! {

// Produce a fixed-length buffer containing the selected values.
//
// Conversion allows for both handles, the vector's four reserved elements, and
// the two elements copied into the boxed slice before the old buffer is released.
fn pack() -> (b: Box<[u32]>)
    ensures b.len() == 2, b[0] == 7, b[1] == 9,
    resources peak(memory) <= value_size(Vec<u32>) + value_size(Box<[u32]>)
        + value_size([u32; 4]) + value_size([u32; 2]),
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
    resources peak(memory) <= value_size([u8; 96]),
{
    let b = pack();
    let c = forward(b);
    assert(c[0] == 7);
    drop(c);
    let scratch = [0u8; 96];
}

}
