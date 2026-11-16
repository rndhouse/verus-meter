// rust_verify/tests/example.rs standalone
// Query a declared allowance before choosing whether to allocate a buffer.
// Inputs: a model-byte budget and an optional positive byte count (default 100).
// Query costs are separate; OS RAM discovery and reservation are future work.
use vstd::prelude::*;

verus! {

#[queryable_peak_memory]
fn allocate(count: u16) -> Vec<u8>
    requires count > 0,
    resources peak(memory) <= 1024 + count,
{
    Vec::<u8>::with_capacity(count as usize)
}

} // verus!

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
