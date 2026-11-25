// This example shows how returning a worker's buffer changes the peak memory
// bound for two workers that use the same mutex. In the scratch example in
// mutex_lifetimes.rs, each worker drops its buffer before unlocking, so the
// peak includes just one scratch reservation.
//
// Here the producer can finish first and leave its buffer in the join handle.
// The caller joins the consumer first. While the producer's result is waiting,
// the consumer can take the lock and allocate its own scratch. Verus Meter
// therefore counts `2 * buffer_capacity * value_size(u8)` reserved bytes.
use std::sync::{Arc, Mutex};
use vstd::prelude::*;

verus! {

/// `make` reserves an empty byte buffer and returns it to the producer.
fn make(buffer_capacity: u16) -> Vec<u8>
    resources peak(memory) <= buffer_capacity * value_size(u8)
        + value_size(buffer_capacity) + value_size(Vec<u8>),
{
    Vec::<u8>::with_capacity(buffer_capacity as usize)
}

type SharedCell = Arc<Mutex<u8>>;
type Guard = std::sync::MutexGuard<'static, u8>;
type LockResult = Result<Guard, std::sync::PoisonError<Guard>>;

/// `worker_frame` counts one worker's captured inputs, lock result, and completion tag.
spec fn worker_frame() -> nat {
    value_size(SharedCell) + value_size(u16) + value_size(u8) + value_size(LockResult)
}

/// `work_budget` counts both buffer reservations and one shared mutex when
/// bounding the peak across the two workers.
spec fn work_budget(buffer_capacity: u16) -> nat {
    // Each buffer reserves room for buffer_capacity elements of type u8.
    let reservation_bytes = (buffer_capacity as nat) * value_size(u8);
    // The producer's output and the consumer's scratch each have a reservation and a Vec header.
    let buffers = 2 * reservation_bytes + 2 * value_size(Vec<u8>);

    // Both Arc handles point to one allocation. Count its mutex once, along
    // with the strong and weak reference counts (one usize each).
    let shared = value_size(Mutex<u8>) + 2 * value_size(usize);

    // The caller holds two join handles. The std handle returns the producer's
    // Vec, and the vstd handle returns () when the consumer finishes.
    let jobs = value_size(std::thread::JoinHandle<Vec<u8>>)
        + value_size(vstd::thread::JoinHandle<()>);

    // Add the caller's u16 parameter and one frame for each worker to the
    // totals above. Each frame includes that worker's own copy of the parameter.
    value_size(buffer_capacity) + shared + jobs + 2 * worker_frame() + buffers
}

/// `work` starts two workers that allocate under the same mutex. It joins the
/// consumer first, so the producer's result can still occupy memory while
/// the consumer uses its scratch buffer.
fn work(buffer_capacity: u16)
    resources peak(memory) <= work_budget(buffer_capacity),
{
    let cell = Arc::new(Mutex::new(0u8));
    let peer = cell.clone();
    let producer = std::thread::spawn(move || {
        let guard = cell.lock();
        let buffer = make(buffer_capacity);
        drop(guard);
        buffer
    });
    let consumer = vstd::thread::spawn(move || {
        let guard = peer.lock();
        let scratch = Vec::<u8>::with_capacity(buffer_capacity as usize);
        drop(scratch);
        drop(guard);
    });

    // The producer's completion record can retain its reservation throughout
    // this first join. The second join moves that reservation to the caller.
    let done = consumer.join();
    let output = producer.join().unwrap();
    drop(output);
}

/// `main` runs the two-worker example with 4 KiB per buffer.
fn main() {
    work(4096);
}

} // verus!
