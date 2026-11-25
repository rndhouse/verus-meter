// This example shows how returning a worker's buffer changes the peak memory
// bound for two workers that use the same mutex. In the scratch example in
// mutex_lifetimes.rs, each worker drops its buffer before unlocking, so the
// peak includes just one scratch reservation.
//
// Here the producer can finish first and leave its buffer in the join handle.
// The caller joins the consumer first. While the producer's result is waiting,
// the consumer can take the lock and allocate its own scratch. Verus Meter
// therefore needs `2 * bytes` for the two reservations.
use std::sync::{Arc, Mutex};
use vstd::prelude::*;

verus! {

fn make(bytes: u16) -> Vec<u8>
    resources peak(memory) <= bytes + value_size(bytes) + value_size(Vec<u8>),
{
    Vec::<u8>::with_capacity(bytes as usize)
}

type SharedCell = Arc<Mutex<u8>>;
type Guard = std::sync::MutexGuard<'static, u8>;
type LockResult = Result<Guard, std::sync::PoisonError<Guard>>;

// Both workers capture the Arc and byte count. Each has a completion tag.
spec fn worker_frame() -> nat {
    value_size(SharedCell) + value_size(u16) + value_size(u8) + value_size(LockResult)
}

// The producer's returned Vec can still own its reservation while the consumer
// owns its scratch. Both workers share one Arc backing and have separate join handles.
spec fn work_budget(bytes: u16) -> nat {
    let buffers = 2 * (bytes as nat) + 2 * value_size(Vec<u8>);
    let shared = value_size(Mutex<u8>) + 2 * value_size(usize);
    let jobs = value_size(std::thread::JoinHandle<Vec<u8>>)
        + value_size(vstd::thread::JoinHandle<()>);
    value_size(bytes) + shared + jobs + 2 * worker_frame() + buffers
}

fn work(bytes: u16)
    resources peak(memory) <= work_budget(bytes),
{
    let cell = Arc::new(Mutex::new(0u8));
    let peer = cell.clone();
    let producer = std::thread::spawn(move || {
        let guard = cell.lock();
        let buffer = make(bytes);
        drop(guard);
        buffer
    });
    let consumer = vstd::thread::spawn(move || {
        let guard = peer.lock();
        let scratch = Vec::<u8>::with_capacity(bytes as usize);
        drop(scratch);
        drop(guard);
    });

    // The producer's completion record can retain its reservation throughout
    // this first join. The second join moves that reservation to the caller.
    let done = consumer.join();
    let output = producer.join().unwrap();
    drop(output);
}

fn main() {
    work(4096);
}

} // verus!
