// Transfer part of a collection while preserving each child's allocation.
//
// This example shows how a loop moves whole buffers between collections.
// Dropping the source releases its remaining buffers and backing storage.
// A current(memory) check accounts for the struct and destination storage.
#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// An owning buffer handle; its heap storage is counted separately.
type Buffer = Vec<u32>;

// Two independent owning collections whose children move between fixed fields.
struct Queues {
    // Buffers waiting to be moved, with independently sized allocations.
    source: Vec<Buffer>,
    // Buffers received in last-element extraction order.
    destination: Vec<Buffer>,
}

// Cover the input struct, counters, and extracted handles. The helper also
// allows for overlapping old and replacement destination storage because
// callers need not reserve it in advance.
// The caller keeps paying for the input allocations during the transfer.
spec fn transfer_budget() -> nat {
    let state = value_size(Queues);
    let counters = 2 * value_size(usize);
    let extracted = 2 * value_size(Buffer);
    let replacement = (2 * 4) * value_size(Buffer);
    state + counters + extracted + 2 * replacement
}

// Move two whole children per iteration, for zero, one, or two batches.
// Entry sizes and loop bounds limit the storage touched by the operation.
fn move_pairs(mut queues: Queues, batches: usize) -> Queues
    requires
        queues.source.len() == 4,
        queues.destination.len() == 0,
        batches <= 2,
    resources peak(memory) <= transfer_budget(),
{
    let mut i = 0usize;
    while i < batches
        invariant
            i <= batches,
            batches <= 2,
            queues.source.len() == 4 - 2 * i,
            queues.destination.len() == 2 * i,
    {
        let first = queues.source.pop().unwrap();
        queues.destination.push(first);
        let second = queues.source.pop().unwrap();
        queues.destination.push(second);
        i += 1;
    }
    queues
}

// Move the last two buffers, then release the source and check memory still live.
// The peak allowance covers both collection buffers, all initial allocations,
// and the transfer helper. The final check covers the struct, destination
// backing storage, and the two transferred buffer allocations.
fn main()
    resources peak(memory) <= 2 * 4 * value_size(Buffer)
        + value_size([u32; 4]) + value_size([u32; 8])
        + value_size([u32; 12]) + value_size([u32; 16]) + transfer_budget(),
{
    let mut source = Vec::<Buffer>::with_capacity(4);
    let a = Vec::<u32>::with_capacity(4);
    source.push(a);
    let b = Vec::<u32>::with_capacity(8);
    source.push(b);
    let c = Vec::<u32>::with_capacity(12);
    source.push(c);
    let d = Vec::<u32>::with_capacity(16);
    source.push(d);
    let destination = Vec::<Buffer>::with_capacity(4);

    let queues = Queues { source, destination };
    let queues = move_pairs(queues, 1);
    drop(queues.source);
    assert(current(memory) <= value_size(Queues) + 4 * value_size(Buffer)
        + value_size([u32; 12]) + value_size([u32; 16]));
}

} // verus!
