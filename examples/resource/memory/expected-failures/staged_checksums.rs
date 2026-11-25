// rust_verify/tests/example.rs expect-failures --- Staging exceeds the streaming section allowance.
// Decode and checksum each input byte as a run of BLOCK_BYTES identical bytes.

use vstd::prelude::*;

verus! {

const BLOCK_BYTES: usize = 128;
type Block = [u8; BLOCK_BYTES];

/// `checksum` adds the bytes in one block.
///
/// At range advancement the block reference and sum stay live alongside the
/// range, its receiver reference, the optional next index, and the index slot.
fn checksum(block: &Block) -> u16
    resources peak(memory) <= ref_size(block) + value_size(u16)
        + value_size(core::ops::Range<usize>) + ref_size(&core::ops::Range<usize>)
        + value_size(Option<usize>) + value_size(usize),
{
    let mut sum = 0u16;
    for index in 0usize..block.len()
        invariant
            sum <= 255 * index,
    {
        sum += block[index] as u16;
    }
    sum
}

// Deliberately use the streaming bound: one decoded block, one saved result,
// and the active checksum call. This omits the staging vector's backing.
fn checksums(input: [u8; 2]) -> Vec<u16>
    resources peak(memory) <= value_size(input) + ref_size(&[u8]) + value_size(Vec<u16>)
        + value_size(Block) + return_size(checksum)
        + peak(checksum),
{
    let packed: &[u8] = &input;
    let mut sums = Vec::new();

    // Both decoded blocks stay live while the checksums are produced.
    resources peak(memory) <= value_size(Block) + return_size(checksum)
        + peak(checksum)
    {
        let mut staged = Vec::new();
        for byte in packed {
            let decoded = [*byte; BLOCK_BYTES];
            staged.push(decoded);
        }
        for decoded in staged {
            sums.push(checksum(&decoded));
        }
    }
    sums
}

} // verus!

fn main() {
    assert_eq!(checksums([1, 2]), vec![128, 256]);
}
