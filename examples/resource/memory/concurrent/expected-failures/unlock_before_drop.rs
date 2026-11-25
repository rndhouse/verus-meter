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

// These fields name the model bytes counted once per outstanding worker.
struct WorkerStorage {
    reserved_handle_slot: Job,
    completion_tag: u8,
    captured_mutex: SharedCell,
    captured_capacity: u16,
    lock_result: LockResult,
}

/// `caller_storage` counts the caller's workspace and the mutex shared by all workers.
spec fn caller_storage() -> nat {
    // The caller owns one Arc. Its backing holds two reference counts and the mutex.
    let shared = value_size(SharedCell) + 2 * value_size(usize) + value_size(Cell);
    // The two inputs and spawn index are u16s. The caller also holds the handle
    // vector and, during a join, one popped handle and its result.
    let caller = 3 * value_size(u16) + value_size(Vec<Job>)
        + value_size(Job) + value_size(std::thread::Result<()>);
    shared + caller
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
    resources peak(memory) <= caller_storage() + worker_count * value_size(WorkerStorage)
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
