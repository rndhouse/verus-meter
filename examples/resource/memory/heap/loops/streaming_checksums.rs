// Decode and checksum each input byte as a run of BLOCK_BYTES identical bytes.

use vstd::prelude::*;

verus! {

const BLOCK_BYTES: usize = 128;
type Block = [u8; BLOCK_BYTES];

// The borrowed loop retains its source, iterator, and two item references.
type ByteIter<'a> = core::slice::Iter<'a, u8>;

// Add the bytes in one block. The maximum partial sum is 255 times the number of bytes read.
fn checksum(block: &Block) -> u16
    resources peak(memory) <= 51,
{
    let mut sum = 0u16;
    for i in 0usize..block.len()
        invariant
            sum <= 255 * i,
    {
        sum += block[i] as u16;
    }
    sum
}

// The output contains one checksum per input byte.
fn checksums(input: [u8; 2]) -> Vec<u16>
    resources peak(memory) <= value_size(input) + ref_size(&[u8]) + value_size(Vec<u16>)
        + value_size(Block) + 2 * return_size(checksum)
        + ref_size(&[u8]) + value_size(ByteIter) + 2 * ref_size(&u8)
        + peak(checksum),
{
    let packed: &[u8] = &input;
    let mut sums = Vec::new();

    resources peak(memory) <= value_size(Block) + 2 * return_size(checksum)
        + ref_size(&[u8]) + value_size(ByteIter) + 2 * ref_size(&u8)
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

fn main() {
    assert_eq!(checksums([1, 2]), vec![128, 256]);
}
