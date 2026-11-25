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

/// `shared_mutex_storage` counts the mutex and the two reference counts shared by all Arc handles.
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

/// `reserve_scratch` returns an empty byte vector. Its bound covers the
/// capacity parameter, the vector header, and the requested element slots.
fn reserve_scratch(buffer_capacity: u16) -> Vec<u8>
    resources peak(memory) <= value_size(buffer_capacity) + value_size(Vec<u8>)
        + buffer_capacity * value_size(u8),
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
