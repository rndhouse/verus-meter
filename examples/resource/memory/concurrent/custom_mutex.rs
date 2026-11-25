// A verified custom guard permits one scratch allocation across n workers.
// The fixed and per-worker terms also cover the loop, handles and protocol calls.
mod protocol;
use protocol::Lock;
use vstd::prelude::*;

verus! {

fn custom_batch(n: u16, b: u16)
    resources peak(memory) <= 512 + 192 * n + b,
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

fn main() {
    custom_batch(4, 4096);
}

} // verus!
