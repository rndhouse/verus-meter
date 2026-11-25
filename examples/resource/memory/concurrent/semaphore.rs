// The range clauses expose the products to ordinary budget arithmetic. Each
// real publication contributes a handle and each successful permit covers its
// own vector until release. Waiting and unsuccessful attempts still use space.
use vstd::prelude::*;
use vstd::resource::semaphore::Semaphore;

verus! {

type Job = std::thread::JoinHandle<()>;
type Shared = std::sync::Arc<Semaphore>;

/// `batch_budget` bounds peak memory for `n` workers sharing `k` permits. At
/// most `min(n, k)` scratch buffers of `b` bytes each can coexist.
spec fn batch_budget(n: u16, k: u16, b: u16) -> nat {
    let shared = value_size(Shared) + 2 * value_size(usize) + value_size(Semaphore);
    let inputs_and_counter = value_size(n) + value_size(k) + value_size(b) + value_size(u16);
    let coordinator = inputs_and_counter + value_size(Vec<Job>)
        + value_size(Job) + value_size(std::thread::Result<()>);
    let count = n as nat;
    // One reserved handle slot and at most one live completion tag per worker.
    let outstanding = count * value_size(Job) + count * value_size(u8);
    let captures = count * value_size(Shared) + count * value_size(b);
    // The verified attempt wrapper peaks at 81 bytes including its reference
    // parameter. Remove that caller slot to use the method workspace here.
    let protocol_workspace = (count * 81 - count * ref_size(&Semaphore)) as nat;
    let attempts = count * value_size(Option<vstd::resource::semaphore::Permit>);
    let scratch = (if n <= k { n as nat } else { k as nat }) * (b as nat);
    shared + coordinator + outstanding + captures + attempts + protocol_workspace + scratch
}

/// `batch` starts and joins workers that each try once for a permit. Only a
/// worker holding a permit allocates scratch, and it frees the buffer before
/// returning the permit.
fn batch(n: u16, k: u16, b: u16)
    requires
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
