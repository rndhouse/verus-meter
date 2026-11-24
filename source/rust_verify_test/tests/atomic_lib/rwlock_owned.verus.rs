// The cell persists across read handles. A writer receives the entire old
// allocation and may release an independently allocated replacement.
verus! {

type BufferCell = RwLock<Vec<u8>, Any>;

fn wrap(v: Vec<u8>) -> BufferCell
    resources peak(memory) <= 400,
{
    RwLock::new(v, Ghost(Any))
}

fn unwrap(cell: BufferCell) -> Vec<u8>
    resources peak(memory) <= 400,
{
    cell.into_inner()
}

fn replace(cell: BufferCell, new: Vec<u8>) -> BufferCell
    resources peak(memory) <= 500,
{
    let (old, writer) = cell.acquire_write();
    writer.release_write(new);
    drop(old);
    cell
}

fn guard<'a>(cell: &'a BufferCell) -> ReadHandle<'a, Vec<u8>, Any>
    resources peak(memory) <= 512,
{
    cell.acquire_read()
}

fn inspect(guard: &ReadHandle<Vec<u8>, Any>) -> usize
    resources peak(memory) <= 512,
{
    guard.borrow().len()
}

fn finish_read(guard: ReadHandle<Vec<u8>, Any>)
    resources peak(memory) <= 512,
{
    guard.release_read();
}

fn buffers(n: usize)
    requires n == 4096,
    resources peak(memory) <= 2 * n + 1500,
{
    let a: Vec<u8> = Vec::with_capacity(n);
    let cell = wrap(a);
    let new: Vec<u8> = Vec::with_capacity(n);
    let cell = replace(cell, new);
    let r = guard(&cell);
    let count = inspect(&r);
    finish_read(r);
    let value = unwrap(cell);
    let other: Vec<u8> = Vec::with_capacity(n);
    drop(value);
    drop(other);
}

fn nested()
    resources peak(memory) <= 2048,
{
    let cell = RwLock::<_, Any>::new(Box::new(Box::new([0u8; 128])), Ghost(Any));
    let (value, writer) = cell.acquire_write();
    writer.release_write(value);
    let value = cell.into_inner();
    drop(value);
}

// Discarding the writer leaves the lock occupied and the value outside it.
fn discard_writer(n: usize)
    requires n <= 4096,
    resources peak(memory) <= n + 1024,
{
    let a: Vec<u8> = Vec::with_capacity(n);
    let cell = RwLock::<_, Any>::new(a, Ghost(Any));
    let (old, writer) = cell.acquire_write();
    drop(writer);
    drop(cell);
    drop(old);
}

} // verus!
