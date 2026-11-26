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

/// `try_acquire_workspace` counts the space used when workers simultaneously
/// try to take a permit by changing the available count from its old value to old minus one.
spec fn try_acquire_workspace(worker_count: nat) -> nat {
    let method_locals = worker_count * ref_size(&Semaphore)  // Each call's reference to the semaphore.
        + worker_count * value_size(usize);                  // The available permit count it read.

    let counter_references =
        worker_count * ref_size(&vstd::atomic::PAtomicUsize);  // One counter reference per attempt.
    let expected_and_replacement =
        2 * (worker_count * value_size(usize));  // The old and proposed counts for each attempt.
    let macro_locals = counter_references + expected_and_replacement;

    // The macro keeps its locals while compare_exchange receives its own arguments.
    let call_arguments = counter_references + expected_and_replacement;
    let results =
        worker_count * value_size(Result<usize, usize>);  // Previous count and success/failure tag.
    method_locals + macro_locals + call_arguments + results
}

/// `batch_budget` bounds peak memory for workers sharing a semaphore. At most
/// `min(worker_count, permit_count)` scratch buffers can coexist. Each reserves
/// `scratch_capacity * value_size(u8)` bytes.
spec fn batch_budget(worker_count: u16, permit_count: u16, scratch_capacity: u16) -> nat {
    let shared = value_size(Shared)    // The coordinator's Arc handle.
        + 2 * value_size(usize)        // The Arc's strong and weak counters, counted once.
        + value_size(Semaphore);       // The single semaphore all workers use.

    let inputs_and_counter = value_size(worker_count)  // Number of workers to start.
        + value_size(permit_count)                     // Number of permits to issue.
        + value_size(scratch_capacity)                 // Number of byte slots each buffer requests.
        + value_size(u16);                             // The workers_spawned loop counter.

    let coordinator = inputs_and_counter
        + value_size(Vec<Job>)                  // The handle vector's header.
        + value_size(Job)                       // The handle popped for this join.
        + value_size(std::thread::Result<()>);  // The result returned by join.

    let count = worker_count as nat;

    let outstanding = count * value_size(Job)  // One reserved slot per worker in the handle vector.
        + count * value_size(u8);              // Each worker's completion tag, counted until join.

    let captures = count * value_size(Shared)    // Each worker's cloned Arc handle.
        + count * value_size(scratch_capacity);  // Its copy of the requested capacity.

    // Every worker can be inside try_acquire, even if no permits are available.
    let protocol_workspace = try_acquire_workspace(count);

    // Each attempt has a result slot, including attempts that return None.
    let attempts = count * value_size(Option<vstd::resource::semaphore::Permit>);

    let max_scratch_buffers = if worker_count <= permit_count {
        count                // At most one live buffer per worker.
    } else {
        permit_count as nat  // At most one live buffer per permit.
    };
    let reservation_bytes = (scratch_capacity as nat) * value_size(u8);  // Reserved bytes per buffer.
    let scratch = max_scratch_buffers * reservation_bytes;

    shared + coordinator + outstanding + captures + attempts + protocol_workspace + scratch
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
