// The writer publishes a new buffer. The reader may run on either side of
// the write, and the joining caller recovers the last published allocation.
verus! {

fn shared()
    resources peak(memory) <= 2048,
{
    let initial = Vec::<u8>::with_capacity(79);
    let lock = std::sync::Arc::new(RwLock::<_, Any>::new(initial, Ghost(Any)));
    let write = lock.clone();
    let read = lock.clone();
    let writer = vstd::thread::spawn(move || {
        let (old, guard) = write.acquire_write();
        let new = Vec::<u8>::with_capacity(821);
        guard.release_write(new);
        drop(old);
    });
    let reader = vstd::thread::spawn(move || {
        let guard = read.acquire_read();
        let view = guard.borrow();
        let count = view.len();
        guard.release_read();
    });
    let writer_done = writer.join();
    let reader_done = reader.join();
    let owned = std::sync::Arc::into_inner(lock);
    match owned {
        Some(cell) => {
            let value = cell.into_inner();
            assert(current(memory) <= 1200);
            drop(value);
        },
        None => { },
    }
}

} // verus!
