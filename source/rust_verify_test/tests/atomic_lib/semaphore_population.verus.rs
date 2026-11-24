// The range clauses expose the products to ordinary budget arithmetic. Each
// real publication contributes a handle and each successful permit covers its
// own vector until release. Waiting and unsuccessful attempts still use space.
use vstd::prelude::*;
use vstd::resource::semaphore::Semaphore;

verus! {

fn batch(n: u16, k: u16, b: u16)
    requires
        0 <= n as int * b as int <= 4294967296int,
        0 <= k as int * b as int <= 4294967296int,
    resources peak(memory) <= 512 + 192 * n + (if n <= k { n } else { k }) * b,
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

fn clients() {
    batch(4, 0, 4096);
    batch(4, 2, 4096);
    batch(2, 4, 4096);
}

} // verus!
