// Helpers borrow a vector while its owner keeps paying for the allocation.
// The verifier infers the reservation needed by append from its length bound
// and checks that the caller supplies it. No capacity annotation is needed.
use vstd::prelude::*;

verus! {

fn append(values: &mut Vec<u32>, capacity: usize, value: u32)
    requires
        old(values).len() < capacity,
    ensures
        final(values)@ == old(values)@.push(value),
    mem_peak <= mem_size(values) + mem_size(capacity) + mem_size(value),
{
    values.push(value);
}

fn count(values: &Vec<u32>) -> (n: usize)
    ensures
        n == values.len(),
    mem_peak <= mem_size(values) + mem_size(usize),
{
    values.len()
}

fn build()
    mem_peak <= mem_size(Vec<u32>) + 2 * mem_size(u32) + mem_peak(append),
{
    let mut values = Vec::<u32>::with_capacity(2);
    append(&mut values, 2, 10);
    append(&mut values, 2, 20);
    let n = count(&values);
    assert(n == 2 && values[0] == 10 && values[1] == 20);
}

fn main() { build(); }

}
