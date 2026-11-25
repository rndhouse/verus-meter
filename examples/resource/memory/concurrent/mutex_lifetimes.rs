// Four workers share a mutex protecting an initially empty vector. Both cases
// publish all four workers before beginning to join them.
use std::sync::{Arc, Mutex};
use vstd::prelude::*;

macro_rules! four_workers {
    ($cell:ident, |$peer:ident| $body:block) => {{
        let $peer = $cell.clone();
        let first = std::thread::spawn(move || $body);
        let $peer = $cell.clone();
        let second = std::thread::spawn(move || $body);
        let $peer = $cell.clone();
        let third = std::thread::spawn(move || $body);
        let $peer = $cell.clone();
        let fourth = std::thread::spawn(move || $body);

        let a = first.join().unwrap();
        let b = second.join().unwrap();
        let c = third.join().unwrap();
        let d = fourth.join().unwrap();
    }};
}

// One requested reservation, shared by the executable allocation and its size formula.
macro_rules! payload_bytes {
    () => { 256 };
}

verus! {

type Cell = Mutex<Vec<Vec<u8>>>;
type SharedCell = Arc<Cell>;
type Job = std::thread::JoinHandle<()>;
type Guard = std::sync::MutexGuard<'static, Vec<Vec<u8>>>;
type LockResult = Result<Guard, std::sync::PoisonError<Guard>>;
type Payload = [u8; payload_bytes!()];

// The coordinator retains one handle and the shared backing throughout the joins.
spec fn shared_cell() -> nat {
    value_size(SharedCell) + 2 * value_size(usize) + value_size(Cell)
}

// Each published worker has a handle, a completion tag and a captured Arc.
spec fn published_worker() -> nat {
    value_size(Job) + value_size(u8) + value_size(SharedCell)
}

// The reservation, its Vec header and the input are live together.
fn temporary(bytes: u16)
    resources peak(memory) <= bytes + value_size(Vec<u8>) + value_size(bytes),
{
    let scratch = Vec::<u8>::with_capacity(bytes as usize);
    drop(scratch);
}

// The coordinator retains its input. Each worker captures its own copy and
// can hold a lock result while another worker runs the helper.
spec fn scratch_frames(bytes: u16) -> nat {
    shared_cell() + value_size(bytes)
        + 4 * (published_worker() + value_size(bytes) + value_size(LockResult))
}

// Only one helper can own its scratch reservation at a time.
fn scratch(bytes: u16)
    resources peak(memory) <= scratch_frames(bytes) + peak(temporary(bytes)),
{
    let cell = Arc::new(Cell::new(Vec::new()));
    four_workers!(cell, |peer| {
        let guard = peer.lock();
        temporary(bytes);
        drop(guard);
    });
    assert(current(memory) <= value_size(bytes) + value_size(SharedCell)
        + 2 * value_size(usize) + value_size(Cell));
    drop(cell);
}

// Each occupied outer slot stores the inner Vec header alongside its separate reservation.
spec fn retained_entry() -> nat {
    value_size(Vec<u8>) + value_size(Payload)
}

// Allow the shared contents and one in-progress push under the guard.
spec fn retained_budget() -> nat {
    let shared = shared_cell() + 4 * retained_entry();
    let workers = 4 * (published_worker() + value_size(LockResult));
    shared + workers + value_size(Guard) + retained_entry()
}

fn retained()
    resources peak(memory) <= retained_budget(),
{
    let cell = Arc::new(Cell::new(Vec::new()));
    four_workers!(cell, |peer| {
        let result = peer.lock();
        if result.is_err() { return; }
        let mut guard = result.unwrap();
        let buffer = Vec::<u8>::with_capacity(payload_bytes!());
        guard.push(buffer);
    });
    assert(current(memory) <= value_size(SharedCell) + 2 * value_size(usize) + value_size(Cell)
        + 4 * (value_size(Vec<u8>) + value_size(Payload)));
    drop(cell);
}

fn main() {
    scratch(4096);
    retained();
}

} // verus!
