// This example shows how to checksum two decoded blocks with room for only one decoded
// block at a time.
//
// Each iteration decodes one byte into a local array. At the second helper call, the
// first checksum remains live in the output.

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

/// `checksums` decodes and checksums one block per iteration.
fn checksums(input: [u8; 2]) -> Vec<u16>
    resources peak(memory) <= value_size(input) + ref_size(&[u8]) + value_size(Vec<u16>)
        + value_size(Block) + return_size(checksum)
        + peak(checksum),
{
    let packed: &[u8] = &input;
    let mut sums = Vec::new();

    // The first sum stays in the output during the second call. Only the current
    // decoded block needs storage inside the loop.
    resources peak(memory) <= value_size(Block) + return_size(checksum)
        + peak(checksum)
    {
        for byte in packed {
            let decoded = [*byte; BLOCK_BYTES];
            sums.push(checksum(&decoded));
        }
    }
    sums
}

} // verus!

/// `main` checks the streamed results for two input bytes.
fn main() {
    assert_eq!(checksums([1, 2]), vec![128, 256]);
}
