// This example shows how to account for children moved between two owning vectors.
//
// The loop moves pairs of buffers. After dropping the source, the caller checks exactly
// which reservations can remain in the destination.

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

/// `transfer_budget` allows for the two queues, loop state, extracted handles, and
/// destination slots.
spec fn transfer_budget() -> nat {
    // The struct contains both vector headers. Its incoming buffers are charged to the caller.
    let state = value_size(Queues);
    // The batch count and iteration index accompany the two moves in each batch.
    let counters = 2 * value_size(usize);
    let extracted = 2 * value_size(Buffer);
    // At two pairs, all four destination slots can hold buffer handles.
    let destination_slots = 4 * value_size(Buffer);
    state + counters + extracted + destination_slots
}

/// `move_pairs` moves two buffers from source to destination on each iteration.
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

/// `main` moves one pair and checks which allocations survive dropping the source.
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
    // Popping takes the last two source buffers, of 16 and 12 elements respectively.
    // The destination still has all four reserved header slots after the source is dropped.
    assert(current(memory) <= value_size(Queues) + 4 * value_size(Buffer)
        + value_size([u32; 12]) + value_size([u32; 16]));
}

} // verus!
