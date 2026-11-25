// rust_verify/tests/example.rs standalone
// This example shows how to query a verified memory bound before deciding whether to
// allocate.
//
// The command takes a budget in model bytes and an optional positive element count
// (default 100). It compares that budget with the declared bound for this input before
// calling the allocator.

use vstd::prelude::*;

verus! {

/// `allocation_memory` counts the parameter, the capacity argument, the vector header,
/// and the reserved elements.
spec fn allocation_memory(count: u16) -> nat {
    let input = value_size(count);
    // The caller supplies a u16, but with_capacity receives a usize.
    let capacity_argument = value_size(usize);
    let buffer_handle = value_size(Vec<u8>);
    // Each requested element reserves one u8 slot, even though the vector is empty.
    let backing = (count as nat) * value_size(u8);
    input + capacity_argument + buffer_handle + backing
}

/// `allocate` returns an empty byte vector with room for the requested number of
/// elements.
#[queryable_peak_memory]
fn allocate(count: u16) -> Vec<u8>
    requires count > 0,
    resources peak(memory) <= allocation_memory(count),
{
    Vec::<u8>::with_capacity(count as usize)
}

} // verus!

/// `main` checks the count and allocates only when the queried bound fits the supplied
/// budget.
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args().skip(1);
    let budget: u64 = arguments.next().ok_or("usage: runtime-query BUDGET [COUNT]")?.parse()?;
    let count = arguments.next().map_or(Ok(100u16), |value| value.parse())?;

    // Establish allocate's precondition independently of the budget query.
    if count == 0 {
        return Err("count must be greater than zero".into());
    }
    let required = allocate::peak_memory_bound(count)
        .map_err(|error| format!("memory query failed: {error}"))?;
    if required.fits_within(budget) {
        let buffer = allocate(count);
        println!("Admitted: allowance {required}, capacity {}", buffer.capacity());
    } else {
        println!("Declined: allowance {required} exceeds budget {budget}");
    }
    Ok(())
}
