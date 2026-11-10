// Temporary heap buffers can share an allowance when their lifetimes do not overlap.
//
// Each buffer has a small owning handle and a separate heap object. Borrowing
// lets a helper use that object while its storage remains charged to the owner.

use vstd::prelude::*;

verus! {

type Buffer = [u8; 16];

// Update an existing buffer without allocating another one.
//
// The helper budgets for its reference; the caller retains the heap object's
// charge. The functional promise lets the caller check the result as well.
fn fill(buffer: &mut Buffer)
    ensures final(buffer)[0] == 7,
    resources peak(memory) <= ref_size(buffer),
{
    buffer[0] = 7;
}

// Reuse one buffer's memory allowance for the next piece of work.
//
// Each scope drops its box before the next scope allocates. The bound includes
// one owning handle, one heap buffer, and the borrowed helper's workspace.
fn main()
    resources peak(memory) <= value_size(Box<Buffer>) + value_size(Buffer) + peak(fill),
{
    {
        let mut first = Box::new([0u8; 16]);
        fill(&mut *first);
        assert(first[0] == 7);
    }
    {
        let mut second = Box::new([0u8; 16]);
        fill(&mut *second);
        assert(second[0] == 7);
    }
    assert(peak(memory) <= value_size(Box<Buffer>) + value_size(Buffer) + peak(fill));
}

}
