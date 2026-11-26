// This example shows how Verus Meter uses a user-defined lock to prove that
// four workers requesting 4 KiB each can hold at most 4 KiB of scratch between them.
//
// The proof in `protocol.rs` establishes that only one guard for this lock
// can exist at a time. Here, each worker tries once to acquire that guard.
// A successful worker reserves its own buffer and frees it before unlocking.
// A worker that misses the lock skips the allocation.
//
// For any worker count, the scratch bound is one worker's requested capacity
// in a nonempty batch and zero in an empty batch.
mod protocol;
use protocol::Lock;
use vstd::prelude::*;

verus! {

type Job = std::thread::JoinHandle<()>;
type Shared = std::sync::Arc<Lock>;

/// Storage counted for each worker, including workers that miss the lock.
struct WorkerStorage<'a> {
    /// The worker's cloned handle to the shared lock.
    lock: Shared,
    /// The scratch capacity captured by the worker.
    scratch_capacity: u16,
    /// The completion tag kept until join.
    completion: u8,
    /// The result of try_enter, which holds the guard on success.
    acquisition: Option<protocol::Guard<'a>>,
}

/// `coordinator_storage` counts the shared lock once and the storage used
/// to start and join the workers.
spec fn coordinator_storage(worker_count: u16) -> nat {
    let shared = value_size(Shared)  // The coordinator's Arc handle.
        + 2 * value_size(usize)      // The Arc's strong and weak counters.
        + value_size(Lock);          // The one lock all workers try to acquire.

    shared + 2 * value_size(u16)                   // The worker count and scratch capacity.
        + value_size(u16)                          // The workers_spawned loop counter.
        + value_size(Vec<Job>)                     // The handle vector's header.
        + (worker_count as nat) * value_size(Job)  // One reserved vector slot per worker.
        + value_size(Job)                          // The handle popped for this join.
        + value_size(std::thread::Result<()>)      // The result returned by join.
}

/// `batch_budget` allows every worker to try the lock concurrently. Only
/// the guard holder can have a live scratch reservation.
spec fn batch_budget(worker_count: u16, scratch_capacity: u16) -> nat {
    let count = worker_count as nat;
    let workers = count * value_size(WorkerStorage)  // Each worker's captures, tag, and lock result.
        + protocol::transition_workspace(count);     // Space used inside the lock methods.

    let scratch = if worker_count == 0 {
        0
    } else {
        (scratch_capacity as nat) * value_size(u8)  // One byte per slot in the guard holder's buffer.
    };
    coordinator_storage(worker_count) + workers + scratch
}

/// `custom_batch` starts and joins workers that each try to acquire the custom
/// lock once. A successful worker frees its scratch before releasing the lock.
fn custom_batch(worker_count: u16, scratch_capacity: u16)
    resources peak(memory) <= batch_budget(worker_count, scratch_capacity),
{
    let lock = std::sync::Arc::new(Lock::new());
    let mut handles = Vec::with_capacity(worker_count as usize);
    let mut workers_spawned = 0u16;
    while workers_spawned < worker_count
        invariant workers_spawned <= worker_count, handles.len() == workers_spawned,
        decreases worker_count - workers_spawned,
    {
        let peer = lock.clone();
        let job = std::thread::spawn(move || {
            if let Some(guard) = peer.try_enter() {
                let scratch = Vec::<u8>::with_capacity(scratch_capacity as usize);
                drop(scratch);  // Free this buffer before another worker can acquire the lock.
                guard.leave();
            }
        });
        handles.push(job);
        workers_spawned += 1;
    }
    while handles.len() > 0
        invariant handles.len() <= worker_count,
        decreases handles.len(),
    {
        let job = handles.pop().unwrap();
        let result = job.join();
    }
}

/// `main` runs four workers sharing one custom lock.
fn main() {
    custom_batch(4, 4096);
}

} // verus!
