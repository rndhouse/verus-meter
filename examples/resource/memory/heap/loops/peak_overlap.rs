// Release temporary work buffers before storing larger results in a loop.
//
// Each iteration extracts a 64-byte buffer from a temporary staging collection.
// Dropping the collection releases its backing; the extracted buffer remains
// allocated until it too is dropped. Earlier 128-byte results stay allocated
// in the destination across iterations.
use vstd::prelude::*;

verus! {

// Build two results within 352 model bytes by releasing each work buffer first.
// The budget covers both retained results, collection backing, and handles.
// Compare the loop allocation overlap example under expected-failures.
fn main()
    resources peak(memory) <= 352,
{
    let mut destination = Vec::<Box<[u8; 128]>>::with_capacity(2);
    let mut i = 0usize;
    while i < 2
        invariant
            i <= 2,
            destination.len() == i,
        decreases 2 - i,
    {
        let mut staging = Vec::<Box<[u8; 64]>>::with_capacity(1);
        let work = Box::new([0u8;64]);
        staging.push(work);
        let old = staging.pop().unwrap();
        drop(staging);
        drop(old);
        let next = Box::new([0u8;128]);
        destination.push(next);
        i += 1;
    }
}

} // verus!
