// rust_verify/tests/example.rs expect-errors --- Intentionally requires unbudgeted growth.
// Growth is supported, but the budget must cover the old and replacement buffers
// simultaneously. This budget only covers the original buffer.

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

    // The replacement allocation exceeds the memory budget at this push.
    values.push(20);
}

}
