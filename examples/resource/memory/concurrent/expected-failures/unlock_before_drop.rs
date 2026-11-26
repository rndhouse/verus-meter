// rust_verify/tests/example.rs expect-failures --- The one-buffer peak bound must fail.
// This example shows how unlocking before freeing scratch can leave a whole
// batch of buffers live at once.
//
// Compare mutex_bounds_peak.rs. Only the order of the two drops changes. After
// unlocking, each worker can pause with its buffer still live. With four
// workers requesting 4 KiB each, all 16 KiB can coexist.
//
// Look for the two `FAIL:` comments. The first marks the bound Verus Meter rejects.
// The second shows where one worker's buffer can overlap another's.
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
    /// One slot in the coordinator's vector, reserved for this worker's join handle.
    reserved_handle_slot: Job,
    /// One model byte for the worker's completion state, counted from spawn until join.
    completion_tag: u8,
    /// The worker's cloned `Arc` handle. All workers share the same mutex allocation.
    captured_mutex: SharedCell,
    /// The worker's copy of the element count passed to `reserve_scratch`.
    captured_capacity: u16,
    /// The result of `peer.lock()`, which holds the guard until the worker drops it.
    lock_result: LockResult,
}

/// `shared_mutex_storage` counts the mutex and the two reference counts shared by all Arc handles.
spec fn shared_mutex_storage() -> nat {
    value_size(Cell) + 2 * value_size(usize)
}

/// `coordinator_storage` counts the locals of the thread that starts and joins the workers.
spec fn coordinator_storage() -> nat {
    let setup = value_size(SharedCell)  // The coordinator's handle to the shared mutex.
        + 3 * value_size(u16)           // The two inputs and the spawn index.
        + value_size(Vec<Job>);         // The handle vector's header.
    setup + value_size(Job)             // The handle popped for this join.
        + value_size(std::thread::Result<()>)  // The result returned by join.
}

/// `reserve_scratch` reserves room for bytes and returns a vector with length zero.
fn reserve_scratch(buffer_capacity: u16) -> Vec<u8>
    resources peak(memory) <=
        value_size(buffer_capacity)          // The u16 parameter itself.
        + value_size(Vec<u8>)                // The vector header.
        + buffer_capacity * value_size(u8),  // One byte per reserved slot, even before the first push.
{
    Vec::<u8>::with_capacity(buffer_capacity as usize)
}

/// `run_workers_budget` allows storage for every worker and at most one live scratch buffer.
///
/// One buffer suffices when each worker frees its scratch before releasing the shared mutex.
spec fn run_workers_budget(worker_count: u16, buffer_capacity: u16) -> nat {
    // Each worker has its own handles, captured values, and lock result.
    let workers = (worker_count as nat) * value_size(WorkerStorage);

    let scratch = if worker_count == 0 {
        0
    } else {
        // reserve_scratch holds its capacity parameter and a Vec header alongside the buffer.
        let reserved_bytes = (buffer_capacity as nat) * value_size(u8);
        value_size(buffer_capacity) + value_size(Vec<u8>) + reserved_bytes
    };

    shared_mutex_storage() + coordinator_storage() + workers + scratch
}

/// `run_workers` starts all the workers and then joins them. With no workers there
/// is no scratch. For a nonempty batch it claims one call's scratch allowance.
fn run_workers(worker_count: u16, buffer_capacity: u16)
    // FAIL: This bound allows only one live scratch buffer.
    resources peak(memory) <= run_workers_budget(worker_count, buffer_capacity),
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
            // FAIL: If this worker pauses here, another can acquire the mutex and
            // reserve its own buffer while this worker still owns scratch.
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
    run_workers(4, 4096);
}

} // verus!
