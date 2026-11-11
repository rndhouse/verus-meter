// Transfer part of a collection while preserving each child's allocation.
//
// Moving the last two buffers leaves the first two with the source. Popping
// children retains collection backing storage; dropping the source releases
// both its surviving children and that backing storage. Only bounds needed
// for memory verification are specified; termination checking is disabled.
#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// One row's owning handle, excluding its separately allocated u32 buffer.
type Row = Vec<u32>;

// Workspace used while the destination remains allocated.
type Workspace = [u8; 1024];

// Two independent owning collections whose children move between fixed fields.
struct Queues {
    // Buffers waiting to be moved, with independently sized allocations.
    source: Vec<Row>,
    // Buffers received in last-element extraction order.
    destination: Vec<Row>,
}

// Cover the input struct, batch count, loop counter, extracted row handles,
// and two possible replacement buffers bounded by twice the four-row limit.
// Input child allocations remain charged to the caller during the helper.
spec fn transfer_workspace() -> nat {
    let state = value_size(Queues);
    let counters = 2 * value_size(usize);
    let extracted = 2 * value_size(Row);
    let replacement = (2 * 4) * value_size(Row);
    state + counters + extracted + 2 * replacement
}

// Move two whole children per iteration, for zero, one, or two batches.
// Entry sizes and loop bounds limit the storage touched by the operation.
fn move_pairs(mut queues: Queues, batches: usize) -> Queues
    requires
        queues.source.len() == 4,
        queues.destination.len() == 0,
        batches <= 2,
    resources peak(memory) <= transfer_workspace(),
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

// Release the source and its remaining children while keeping the destination.
// The final bound adds the struct, four destination row slots, the two
// transferred buffer allocations, and the named workspace.
fn main()
    resources peak(memory) <= value_size(Queues) + 4 * value_size(Row)
        + value_size([u32; 16]) + value_size([u32; 12]) + value_size(Workspace),
{
    let mut source = Vec::<Row>::with_capacity(4);
    let a = Vec::<u32>::with_capacity(4);
    source.push(a);
    let b = Vec::<u32>::with_capacity(8);
    source.push(b);
    let c = Vec::<u32>::with_capacity(12);
    source.push(c);
    let d = Vec::<u32>::with_capacity(16);
    source.push(d);
    let destination = Vec::<Row>::with_capacity(4);

    let queues = Queues { source, destination };
    let queues = move_pairs(queues, 1);
    drop(queues.source);
    let scratch: Workspace = [0u8;1024];
}

} // verus!
