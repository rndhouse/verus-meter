// This example shows how a semaphore limits scratch memory across workers.
// With four workers and two permits, at most two scratch buffers can exist
// at once. All four workers still need space for their handles and inputs.
use vstd::prelude::*;
use vstd::resource::semaphore::Semaphore;

verus! {

type Job = std::thread::JoinHandle<()>;
type Shared = std::sync::Arc<Semaphore>;

/// `try_acquire_workspace` bounds the space workers use inside the semaphore's
/// compare-exchange. A wrapper taking `&Semaphore` also holds its own parameter,
/// so its peak for one call is `ref_size(&Semaphore) + try_acquire_workspace(1)`.
spec fn try_acquire_workspace(worker_count: nat) -> nat {
    // Each method call keeps its receiver and the available count it read.
    let method_locals = worker_count * ref_size(&Semaphore) + worker_count * value_size(usize);

    // The atomic macro borrows the counter and saves two usize operands:
    // the expected count and its replacement (one fewer available slot).
    let counter_references = worker_count * ref_size(&vstd::atomic::PAtomicUsize);
    let expected_and_replacement = 2 * (worker_count * value_size(usize));
    let macro_locals = counter_references + expected_and_replacement;

    // The compare-exchange call takes a receiver reference and copies both
    // operands. Its result holds the previous count and a success/failure tag.
    let call_arguments = counter_references + expected_and_replacement;
    let results = worker_count * value_size(Result<usize, usize>);
    method_locals + macro_locals + call_arguments + results
}

/// `batch_budget` bounds peak memory for workers sharing a semaphore. At most
/// `min(worker_count, permit_count)` buffers of `scratch_capacity` bytes can coexist.
spec fn batch_budget(worker_count: u16, permit_count: u16, scratch_capacity: u16) -> nat {
    // The caller owns one Arc. Its backing holds the semaphore and the strong
    // and weak reference counts shared by all the workers.
    let shared = value_size(Shared) + 2 * value_size(usize) + value_size(Semaphore);

    // The caller keeps its input parameters and the loop counter used to spawn workers.
    let inputs_and_counter = value_size(worker_count) + value_size(permit_count)
        + value_size(scratch_capacity) + value_size(u16);

    // The caller also owns the handle vector. During a join, it takes out one
    // handle and receives the thread's result.
    let coordinator = inputs_and_counter + value_size(Vec<Job>)
        + value_size(Job) + value_size(std::thread::Result<()>);

    // Use the worker count as a natural number for the per-worker terms below.
    let count = worker_count as nat;

    // The vector reserves one handle slot per worker. Each outstanding
    // worker can also have a one-byte completion tag.
    let outstanding = count * value_size(Job) + count * value_size(u8);

    // Each worker takes its own Arc handle to the same semaphore and a copy of
    // the requested scratch capacity.
    let captures = count * value_size(Shared) + count * value_size(scratch_capacity);

    // Every worker can be inside try_acquire, even if no permits are available.
    let protocol_workspace = try_acquire_workspace(count);

    // Each worker receives its own optional permit from the acquisition call.
    let attempts = count * value_size(Option<vstd::resource::semaphore::Permit>);

    // Each scratch buffer requires both a worker and a permit. Whichever runs
    // out first limits how many reservations can overlap.
    let max_scratch_buffers = if worker_count <= permit_count { count } else { permit_count as nat };
    let scratch = max_scratch_buffers * (scratch_capacity as nat) * value_size(u8);

    // Count shared and caller storage once, then add the worker storage and
    // the scratch reservations that can coexist.
    shared + coordinator + outstanding + captures + attempts + protocol_workspace + scratch
}

/// `batch` starts and joins workers that each try once for a permit. Only a
/// worker holding a permit allocates scratch, and it frees the buffer before
/// returning the permit.
fn batch(worker_count: u16, permit_count: u16, scratch_capacity: u16)
    requires
        // Give the verifier the range of each product that can appear in the
        // scratch bound, depending on whether workers or permits run out first.
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
                drop(scratch);
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
    batch(4, 0, 4096);
    batch(4, 2, 4096);
    batch(2, 4, 4096);
}

} // verus!
