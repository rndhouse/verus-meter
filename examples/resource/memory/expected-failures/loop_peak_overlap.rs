// rust_verify/tests/example.rs expect-failures --- A later iteration overlaps work and result allocations.
// Keep an extracted work buffer alive while allocating its result.
//
// The first iteration fits because no earlier result remains in the destination.
// On the second iteration, a 64-byte work buffer and two 128-byte results exceed
// 352 model bytes once collection backing and owning handles are included.
// Compare heap/loops/peak_overlap.rs for the passing release order.
use vstd::prelude::*;

verus! {

// Deliberately retain the extracted buffer until its result is stored.
// The reusable loop check must cover the results retained by earlier iterations.
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
        let next = Box::new([0u8;128]);
        destination.push(next);
        drop(old);
        i += 1;
    }
}

} // verus!
