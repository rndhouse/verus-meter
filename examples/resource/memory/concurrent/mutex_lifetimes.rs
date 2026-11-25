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

verus! {

type Cell = Mutex<Vec<Vec<u8>>>;

// The two-byte input and the Vec header occupy 26 bytes alongside its reservation.
fn temporary(bytes: u16)
    resources peak(memory) <= bytes + 26,
{
    let scratch = Vec::<u8>::with_capacity(bytes as usize);
    drop(scratch);
}

// Each worker holds its lock result across the helper, including its cleanup.
// Both variants of a blocking lock result own the guard. The 256 fixed bytes
// allow for the shared cell, captures, handles, completion tags and working frames.
fn scratch(bytes: u16)
    resources peak(memory) <= bytes + 256,
{
    let cell = Arc::new(Cell::new(Vec::new()));
    four_workers!(cell, |peer| {
        let guard = peer.lock();
        temporary(bytes);
        drop(guard);
    });
    // The input adds two bytes to the 57-byte empty shared cell and handle.
    assert(current(memory) <= 59);
    drop(cell);
}

// The outer Vec starts with zero reservation. Each successful push retains a
// 24-byte occupied slot (the inner Vec header) and its 256-byte reservation.
// The 57 bytes cover the remaining Arc handle, count fields, mutex and outer
// Vec header. The peak allowance combines that final contents bound with one
// 256-byte reservation in construction under the lock and 48 bytes per worker
// for captures, working frames, join handles and completion tags.
fn retained()
    resources peak(memory) <= 57 + 4 * (24 + 256) + 256 + 4 * 48,
{
    let cell = Arc::new(Cell::new(Vec::new()));
    four_workers!(cell, |peer| {
        let result = peer.lock();
        if result.is_err() { return; }
        let mut guard = result.unwrap();
        let buffer = Vec::<u8>::with_capacity(256);
        guard.push(buffer);
    });
    assert(current(memory) <= 57 + 4 * (24 + 256));
    drop(cell);
}

fn main() {
    scratch(4096);
    retained();
}

} // verus!
