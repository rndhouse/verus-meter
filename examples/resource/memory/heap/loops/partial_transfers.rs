// Transfer part of a collection while preserving each child's allocation.
//
// Moving the last two buffers leaves the first two with the source. Popping
// children retains collection backing storage; dropping the source releases
// both its surviving children and that backing storage.
use vstd::prelude::*;

verus! {

// Two independent owning collections whose children move between fixed fields.
struct Queues {
    // Buffers waiting to be moved, with independently sized allocations.
    source: Vec<Vec<u32>>,
    // Buffers received in last-element extraction order.
    destination: Vec<Vec<u32>>,
}

// Move two whole children per iteration, for zero, one, or two batches.
// The caller retains input allocation charges during the call. This allowance
// covers the helper's handles and any new destination backing storage.
fn move_pairs(mut queues: Queues, batches: usize) -> (result: Queues)
    requires
        queues.source.len() == 4,
        queues.destination.len() == 0,
        batches <= 2,
    ensures
        result.source.len() == 4 - 2 * batches,
        result.destination.len() == 2 * batches,
    resources peak(memory) <= 512,
{
    let mut i = 0usize;
    while i < batches
        invariant
            i <= batches,
            batches <= 2,
            queues.source.len() == 4 - 2 * i,
            queues.destination.len() == 2 * i,
        decreases batches - i,
    {
        let first = queues.source.pop().unwrap();
        queues.destination.push(first);
        let second = queues.source.pop().unwrap();
        queues.destination.push(second);
        i += 1;
    }
    queues
}

// Keep the transferred buffers while releasing the source and its remainder.
// At the final peak, the 48-byte struct, 96-byte destination backing, and
// transferred buffers of 64 and 48 bytes coexist with 1024 bytes of workspace.
fn main()
    resources peak(memory) <= 1280,
{
    let mut source = Vec::<Vec<u32>>::with_capacity(4);
    let a = Vec::<u32>::with_capacity(4);
    source.push(a);
    let b = Vec::<u32>::with_capacity(8);
    source.push(b);
    let c = Vec::<u32>::with_capacity(12);
    source.push(c);
    let d = Vec::<u32>::with_capacity(16);
    source.push(d);
    let destination = Vec::<Vec<u32>>::with_capacity(4);

    let queues = Queues { source, destination };
    let queues = move_pairs(queues, 1);
    assert(queues.source.len() == 2);
    assert(queues.destination.len() == 2);
    drop(queues.source);
    let scratch = [0u8;1024];
}

} // verus!
