// rust_verify/tests/example.rs ignore --- Compiled coverage in verus_meter_runtime/tests/query.rs supplies the runtime dependency.
// Query a declared allowance before choosing whether to allocate a buffer.
// Run with an explicit model-byte budget; OS memory discovery is separate work.
use vstd::prelude::*;

verus_builtin_macros::verus! {

#[queryable_peak_memory]
fn allocate(count: u16) -> Vec<u8>
    resources peak(memory) <= 1024 + count,
{
    Vec::<u8>::with_capacity(count as usize)
}

} // verus!

fn main() {
    let budget: u64 = std::env::args().nth(1).expect("supply a model-byte budget")
        .parse().expect("budget must be an unsigned integer");
    let count = std::env::args().nth(2).map_or(100u16, |value| {
        value.parse().expect("count must fit u16")
    });
    let required = allocate::peak_memory_bound(count).expect("example query is valid");
    if required.fits_within(budget) {
        let buffer = allocate(count);
        println!("Admitted: allowance {required}, capacity {}", buffer.capacity());
    } else {
        println!("Declined: allowance {required} exceeds budget {budget}");
    }
}
