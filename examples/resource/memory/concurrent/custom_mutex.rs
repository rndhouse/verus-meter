// A verified custom guard permits one scratch allocation across n workers.
// The fixed and per-worker terms also cover the loop, handles and protocol calls.
mod protocol;
use protocol::Lock;
use vstd::prelude::*;

verus! {

type Job = std::thread::JoinHandle<()>;
type Shared = std::sync::Arc<Lock>;

/// `batch_budget` bounds peak memory for all workers. The lock admits one guard
/// at a time, so at most one worker contributes a scratch buffer.
spec fn batch_budget(n: u16, b: u16) -> nat {
    let shared = value_size(Shared) + 2 * value_size(usize) + value_size(Lock);
    let inputs_and_counter = value_size(n) + value_size(b) + value_size(u16);
    let coordinator = inputs_and_counter + value_size(Vec<Job>)
        + value_size(Job) + value_size(std::thread::Result<()>);
    let count = n as nat;
    // One reserved handle slot and at most one live completion tag per worker.
    let outstanding = count * value_size(Job) + count * value_size(u8);
    let captures = count * value_size(Shared) + count * value_size(b);
    let protocol_workspace = protocol::transition_workspace(count);
    let attempts = count * value_size(Option<protocol::Guard>);
    let scratch = if n == 0 { 0nat } else { b as nat };
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
