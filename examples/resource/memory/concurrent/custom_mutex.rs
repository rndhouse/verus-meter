// This example shows how a user-defined lock can justify a one-buffer scratch
// bound for any number of workers. Its proof allows only one guard at a time,
// and each worker frees its buffer before giving up that guard.
mod protocol;
use protocol::Lock;
use vstd::prelude::*;

verus! {

type Job = std::thread::JoinHandle<()>;
type Shared = std::sync::Arc<Lock>;

/// `batch_budget` bounds peak memory for all workers. The lock admits one guard
/// at a time, so at most one worker contributes a scratch buffer.
spec fn batch_budget(n: u16, b: u16) -> nat {
    // The caller owns one Arc. Its backing holds the lock and the strong
    // and weak reference counts shared by all the workers.
    let shared = value_size(Shared) + 2 * value_size(usize) + value_size(Lock);

    // The caller keeps its input parameters and the loop counter used to spawn workers.
    let inputs_and_counter = value_size(n) + value_size(b) + value_size(u16);

    // The caller also owns the handle vector. During a join, it takes out one
    // handle and receives the thread's result.
    let coordinator = inputs_and_counter + value_size(Vec<Job>)
        + value_size(Job) + value_size(std::thread::Result<()>);

    // Use the worker count as a natural number for the per-worker terms below.
    let count = n as nat;

    // The vector reserves one handle slot per worker. Each outstanding
    // worker can also have a one-byte completion tag.
    let outstanding = count * value_size(Job) + count * value_size(u8);

    // Each worker takes its own Arc handle to the same lock and a copy of
    // the requested scratch capacity.
    let captures = count * value_size(Shared) + count * value_size(b);

    // The lock supplies a bound for the space workers use inside its methods.
    let protocol_workspace = protocol::transition_workspace(count);

    // Each worker receives its own optional guard from the acquisition call.
    let attempts = count * value_size(Option<protocol::Guard>);

    // Only the guard holder can reserve scratch. An empty batch reserves none.
    let scratch = if n == 0 { 0nat } else { b as nat };

    // Count shared and caller storage once, then add the worker storage and
    // the scratch reservations that can coexist.
    shared + coordinator + outstanding + captures + attempts + protocol_workspace + scratch
}

/// `custom_batch` starts and joins workers that each try to acquire the custom
/// lock once. A successful worker frees its scratch before releasing the lock.
fn custom_batch(n: u16, b: u16)
    resources peak(memory) <= batch_budget(n, b),
{
    let lock = std::sync::Arc::new(Lock::new());
    let mut handles = Vec::with_capacity(n as usize);
    let mut i = 0u16;
    while i < n
        invariant i <= n, handles.len() == i,
        decreases n - i,
    {
        let peer = lock.clone();
        let job = std::thread::spawn(move || {
            if let Some(guard) = peer.try_enter() {
                let scratch = Vec::<u8>::with_capacity(b as usize);
                drop(scratch);
                guard.leave();
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

/// `main` runs four workers sharing one custom lock.
fn main() {
    custom_batch(4, 4096);
}

} // verus!
