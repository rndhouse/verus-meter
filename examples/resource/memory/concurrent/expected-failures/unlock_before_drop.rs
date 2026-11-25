// rust_verify/tests/example.rs expect-failures --- The one-buffer peak bound must fail.
// This example shows how unlocking before freeing scratch can leave a whole
// batch of buffers live at once.
//
// Compare counted_mutex.rs. Only the order of the two drops changes. After
// unlocking, each worker can pause with its buffer still live. With four
// workers requesting 4 KiB each, all 16 KiB can coexist.
use std::sync::{Arc, Mutex};
use vstd::prelude::*;

verus! {

type Cell = Mutex<()>;
type SharedCell = Arc<Cell>;
type Job = std::thread::JoinHandle<()>;
type Guard = std::sync::MutexGuard<'static, ()>;
type LockResult = Result<Guard, std::sync::PoisonError<Guard>>;

/// `batch_storage` counts the caller, the shared mutex, and the storage for
/// the outstanding workers. The contract adds scratch separately.
spec fn batch_storage(worker_count: u16, buffer_capacity: u16) -> nat {
    // The caller owns one Arc. All clones share its two counts and one mutex.
    let shared = value_size(SharedCell) + 2 * value_size(usize) + value_size(Cell);

    // Count the two inputs, spawn index, and handle vector. Joining also
    // needs a local for the popped handle and one for the join result.
    let caller = value_size(worker_count) + value_size(buffer_capacity) + value_size(u16)
        + value_size(Vec<Job>) + value_size(Job) + value_size(std::thread::Result<()>);

    // The vector reserves one handle slot per worker. Each outstanding worker
    // also has a completion tag, even if it finishes before the caller joins it.
    let count = worker_count as nat;
    let outstanding = count * value_size(Job) + count * value_size(u8);

    // Each worker captures its own Arc and capacity and has a slot for its lock result.
    let captures = count * value_size(SharedCell) + count * value_size(buffer_capacity);
    let locks = count * value_size(LockResult);
    shared + caller + outstanding + captures + locks
}

/// `reserve_scratch` returns an empty byte vector. Its bound covers the
/// capacity parameter, the vector header, and the requested element slots.
fn reserve_scratch(buffer_capacity: u16) -> Vec<u8>
    resources peak(memory) <= value_size(buffer_capacity) + value_size(Vec<u8>)
        + buffer_capacity * value_size(u8),
{
    Vec::<u8>::with_capacity(buffer_capacity as usize)
}

/// `batch` starts all the workers and then joins them. With no workers there
/// is no scratch. For a nonempty batch it claims one call's scratch allowance.
fn batch(worker_count: u16, buffer_capacity: u16)
    resources peak(memory) <= batch_storage(worker_count, buffer_capacity)
        + if worker_count == 0 { 0 } else { peak(reserve_scratch(buffer_capacity)) },
{
    let cell = Arc::new(Cell::new(()));
    let mut handles = Vec::with_capacity(worker_count as usize);
    let mut spawned = 0u16;
    while spawned < worker_count
        decreases worker_count - spawned,
    {
        let peer = cell.clone();
        let job = std::thread::spawn(move || {
            let guard = peer.lock();
            let scratch = reserve_scratch(buffer_capacity);
            drop(guard);
            drop(scratch);
        });
        handles.push(job);
        spawned += 1;
    }
    while handles.len() > 0
        decreases handles.len(),
    {
        let job = handles.pop().unwrap();
        let result = job.join();
    }
}

/// `main` runs four workers requesting 4 KiB of scratch apiece.
fn main() {
    batch(4, 4096);
}

} // verus!
