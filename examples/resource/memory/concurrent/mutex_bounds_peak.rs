// This example shows how any number of workers can each request 4 KiB of
// scratch while using at most 4 KiB of scratch between them.
//
// The worker count and buffer capacity are both inputs. The coordinator starts every
// worker before joining any. Each worker holds the same mutex from the call
// that reserves its buffer until it frees that buffer. Only the handles and
// other per-worker storage scale with the worker count.
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

/// `shared_mutex_storage` counts the mutex and its Arc's strong and weak counters once,
/// regardless of how many workers clone the handle.
spec fn shared_mutex_storage() -> nat {
    value_size(Cell) + 2 * value_size(usize)
}

/// `coordinator_storage` counts the locals of the thread that starts and joins the workers.
spec fn coordinator_storage() -> nat {
    // The coordinator holds one Arc, two u16 inputs, the u16 spawn index, and the handle vector.
    let setup = value_size(SharedCell) + 3 * value_size(u16) + value_size(Vec<Job>);
    // At each join, it holds one popped handle and receives one result.
    setup + value_size(Job) + value_size(std::thread::Result<()>)
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
/// is no scratch. Otherwise, one call's allowance covers all scratch lifetimes.
fn run_workers(worker_count: u16, buffer_capacity: u16)
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
            drop(scratch);
            drop(guard);
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
