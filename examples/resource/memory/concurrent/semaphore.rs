// This example shows how a semaphore limits scratch memory across workers.
// With four workers and two permits, at most two scratch buffers can exist
// at once. All four workers still need space for their handles and inputs.
use vstd::prelude::*;
use vstd::resource::semaphore::Semaphore;

verus! {

type Job = std::thread::JoinHandle<()>;
type Shared = std::sync::Arc<Semaphore>;

/// `batch_budget` bounds peak memory for `n` workers sharing `k` permits. At
/// most `min(n, k)` scratch buffers of `b` bytes each can coexist.
spec fn batch_budget(n: u16, k: u16, b: u16) -> nat {
    // The caller owns one Arc. Its backing holds the semaphore and the strong
    // and weak reference counts shared by all the workers.
    let shared = value_size(Shared) + 2 * value_size(usize) + value_size(Semaphore);

    // The caller keeps its input parameters and the loop counter used to spawn workers.
    let inputs_and_counter = value_size(n) + value_size(k) + value_size(b) + value_size(u16);

    // The caller also owns the handle vector. During a join, it takes out one
    // handle and receives the thread's result.
    let coordinator = inputs_and_counter + value_size(Vec<Job>)
        + value_size(Job) + value_size(std::thread::Result<()>);

    // Use the worker count as a natural number for the per-worker terms below.
    let count = n as nat;

    // The vector reserves one handle slot per worker. Each outstanding
    // worker can also have a one-byte completion tag.
    let outstanding = count * value_size(Job) + count * value_size(u8);

    // Each worker takes its own Arc handle to the same semaphore and a copy of
    // the requested scratch capacity.
    let captures = count * value_size(Shared) + count * value_size(b);

    // The verified attempt wrapper peaks at 81 bytes including its reference
    // parameter. Remove that caller slot to use the method workspace here.
    let protocol_workspace = (count * 81 - count * ref_size(&Semaphore)) as nat;

    // Each worker receives its own optional permit from the acquisition call.
    let attempts = count * value_size(Option<vstd::resource::semaphore::Permit>);

    // Each scratch buffer requires both a worker and a permit. Whichever runs
    // out first limits how many reservations can overlap.
    let scratch = (if n <= k { n as nat } else { k as nat }) * (b as nat);

    // Count shared and caller storage once, then add the worker storage and
    // the scratch reservations that can coexist.
    shared + coordinator + outstanding + captures + attempts + protocol_workspace + scratch
}

/// `batch` starts and joins workers that each try once for a permit. Only a
/// worker holding a permit allocates scratch, and it frees the buffer before
/// returning the permit.
fn batch(n: u16, k: u16, b: u16)
    requires
        // Give the verifier the range of each product that can appear in the
        // scratch bound, depending on whether workers or permits run out first.
        0 <= n as int * b as int <= u32::MAX as int,
        0 <= k as int * b as int <= u32::MAX as int,
    resources peak(memory) <= batch_budget(n, k, b),
{
    let semaphore = std::sync::Arc::new(Semaphore::new(k as usize));
    let mut handles = Vec::with_capacity(n as usize);
    let mut i = 0u16;
    while i < n
        invariant i <= n, handles.len() == i,
        decreases n - i,
    {
        let peer = semaphore.clone();
        let job = std::thread::spawn(move || {
            if let Some(permit) = peer.try_acquire() {
                let scratch = Vec::<u8>::with_capacity(b as usize);
                drop(scratch);
                permit.release();
            }
        });
        handles.push(job);
        i += 1;
    }
    while handles.len() > 0
        invariant handles.len() <= n,
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
