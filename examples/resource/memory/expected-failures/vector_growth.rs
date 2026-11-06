// rust_verify/tests/example.rs expect-errors --- Intentionally requires unbudgeted growth.
// A vector cannot outgrow the capacity covered by its memory allowance.
//
// An ordinary Rust vector could grow here. The memory contract requires each
// push to stay within the original reservation, so verification rejects it.

use vstd::prelude::*;

verus! {

// Try to keep two numbers in storage reserved for only one.
//
// The first push fits. The second needs additional backing storage that the
// contract has not allowed for.
fn main()
    mem_peak <= mem_size(Vec<u32>) + mem_size(u32),
{
    let mut values = Vec::<u32>::with_capacity(1);
    values.push(10);

    // Verus reports the capacity violation at this push: the reservation is full.
    values.push(20);
}

}
