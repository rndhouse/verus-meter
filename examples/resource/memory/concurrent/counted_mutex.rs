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

/// `run_workers_budget` counts every worker and allows one scratch reservation for a nonempty batch.
spec fn run_workers_budget(worker_count: u16, buffer_capacity: u16) -> nat {
    // One call to reserve_scratch holds its parameter, a Vec header, and the reserved bytes.
    let reservation = (buffer_capacity as nat) * value_size(u8);
    let one_call = value_size(buffer_capacity) + value_size(Vec<u8>) + reservation;
    shared_mutex_storage() + coordinator_storage()
        + (worker_count as nat) * value_size(WorkerStorage)
        + if worker_count == 0 { 0 } else { one_call }
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
