// This example shows how Verus Meter proves that four workers sharing two semaphore
// permits can hold at most 8 KiB of scratch at once when each requests 4 KiB.
//
// A permit gives one worker at a time permission to reserve its own buffer.
// Each worker tries once to get a permit. If it gets one, it frees its buffer
// before returning the permit for another worker to use. Otherwise it skips the allocation.
//
// The proof covers any worker count, permit count, and scratch capacity allowed
// by `batch`. Each live buffer needs both a worker and a permit, so the smaller
// count limits the scratch reservations. All workers can be trying to acquire
// a permit at the same time, so the bound also counts space for every attempt.
use vstd::prelude::*;
use vstd::resource::semaphore::Semaphore;

verus! {

type Job = std::thread::JoinHandle<()>;
type Shared = std::sync::Arc<Semaphore>;

/// The three operands of the atomic operation that attempts to take one permit.
struct CounterUpdate<'a> {
    /// The counter the operation will update.
    counter: &'a vstd::atomic::PAtomicUsize,
    /// The available count the worker read.
    expected: usize,
    /// One fewer permit if the count still matches.
    replacement: usize,
}

/// Source-level storage live during one compare_exchange call inside try_acquire.
struct PermitAttemptStorage<'a> {
    /// The method's receiver.
    semaphore: &'a Semaphore,
    /// The available permit count read by the method.
    available: usize,
    /// The atomic macro keeps these locals during the call.
    saved_operands: CounterUpdate<'a>,
    /// The call receives its own copies of those operands.
    call_arguments: CounterUpdate<'a>,
    /// The previous count and a success/failure tag.
    result: Result<usize, usize>,
}

/// Storage counted for each worker, including workers that receive no permit.
struct WorkerStorage<'a> {
    /// The worker's cloned Arc handle.
    semaphore: Shared,
    /// The scratch capacity captured by the worker.
    scratch_capacity: u16,
    /// The completion tag kept until join.
    completion: u8,
    /// Workspace used inside try_acquire.
    attempt: PermitAttemptStorage<'a>,
    /// The permit returned by try_acquire, or None.
    result: Option<vstd::resource::semaphore::Permit<'a>>,
}

/// `coordinator_storage` counts the shared semaphore once and the storage
/// that `batch` uses to start and join its workers.
spec fn coordinator_storage(worker_count: u16) -> nat {
    let shared = value_size(Shared)  // The coordinator's Arc handle.
        + 2 * value_size(usize)      // The Arc's strong and weak counters.
        + value_size(Semaphore);     // The semaphore all workers use.

    shared + 3 * value_size(u16)                   // The three batch inputs.
        + value_size(u16)                          // The workers_spawned loop counter.
        + value_size(Vec<Job>)                     // The handle vector's header.
        + (worker_count as nat) * value_size(Job)  // One reserved vector slot per worker.
        + value_size(Job)                          // The handle popped for this join.
        + value_size(std::thread::Result<()>)      // The result returned by join.
}

/// `batch_budget` allows every worker to try for a permit at once. Only
/// workers holding a permit can have a live scratch reservation.
spec fn batch_budget(worker_count: u16, permit_count: u16, scratch_capacity: u16) -> nat {
    let count = worker_count as nat;
    let max_scratch_buffers = if worker_count <= permit_count {
        count                // At most one live buffer per worker.
    } else {
        permit_count as nat  // At most one live buffer per permit.
    };
    let reservation_bytes = (scratch_capacity as nat) * value_size(u8);  // Reserved bytes per buffer.

    coordinator_storage(worker_count) + count * value_size(WorkerStorage)
        + max_scratch_buffers * reservation_bytes
}

/// `batch` starts and joins workers that each try once for a permit. Only a
/// worker holding a permit allocates scratch, and it frees the buffer before
/// returning the permit.
fn batch(worker_count: u16, permit_count: u16, scratch_capacity: u16)
    requires
        // Both products fit in u32 for u16 inputs. State this for either branch of the bound.
        0 <= worker_count as int * scratch_capacity as int <= u32::MAX as int,
        0 <= permit_count as int * scratch_capacity as int <= u32::MAX as int,
    resources peak(memory) <= batch_budget(worker_count, permit_count, scratch_capacity),
{
    let semaphore = std::sync::Arc::new(Semaphore::new(permit_count as usize));
    let mut handles = Vec::with_capacity(worker_count as usize);
    let mut workers_spawned = 0u16;
    while workers_spawned < worker_count
        invariant workers_spawned <= worker_count, handles.len() == workers_spawned,
        decreases worker_count - workers_spawned,
    {
        let peer = semaphore.clone();
        let job = std::thread::spawn(move || {
            if let Some(permit) = peer.try_acquire() {
                let scratch = Vec::<u8>::with_capacity(scratch_capacity as usize);
                drop(scratch);  // Free this buffer before another worker can reuse the permit.
                permit.release();
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

/// `main` runs batches with zero permits, fewer permits than workers, and
/// more permits than workers.
fn main() {
    batch(4, 0, 4096); // No permits: no scratch reservations.
    batch(4, 2, 4096); // Two permits limit four workers to 8 KiB of scratch.
    batch(2, 4, 4096); // Two workers can use at most 8 KiB even with permits to spare.
}

} // verus!
