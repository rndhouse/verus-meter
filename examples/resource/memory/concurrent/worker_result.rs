// A completed worker can own a buffer while another worker holds the mutex.
use std::sync::{Arc, Mutex};
use vstd::prelude::*;

verus! {

fn make(bytes: u16) -> Vec<u8>
    resources peak(memory) <= bytes + 26,
{
    Vec::<u8>::with_capacity(bytes as usize)
}

fn work(bytes: u16)
    resources peak(memory) <= 2 * bytes + 256,
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
