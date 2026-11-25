// This example shows how successive heap allocations can share one buffer's allowance.
//
// Each box owns a heap array. A helper borrows that array, and each scope releases its
// box before the next allocation.

use vstd::prelude::*;

verus! {

type Buffer = [u8; 16];

/// `fill` updates the borrowed array within the allowance for one reference.
///
/// The helper budgets for its reference; the caller retains the heap object's
/// charge. The functional promise lets the caller check the result as well.
fn fill(buffer: &mut Buffer)
    ensures final(buffer)[0] == 7,
    resources peak(memory) <= ref_size(buffer),
{
    buffer[0] = 7;
}

/// `main` uses two heap buffers in sequence with room for one box, its array, and the
/// helper.
///
/// Each scope drops its box before the next scope allocates. The bound includes
/// one owning handle, one heap buffer, and the borrowed helper's workspace.
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
