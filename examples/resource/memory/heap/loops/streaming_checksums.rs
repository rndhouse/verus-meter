// Decode and checksum each input byte as a run of 64 identical bytes.
// The checksum vector has room for both results before the scratch section begins.

use vstd::prelude::*;

verus! {

type Block = [u8; 64];

// Add all 64 bytes. The maximum partial sum is 255 times the number of bytes read.
fn checksum(block: &Block) -> u16
    resources peak(memory) <= 52,
{
    let mut sum = 0u16;
    for i in 0usize..64
        invariant
            sum <= 255 * i,
    {
        sum += block[i] as u16;
    }
    sum
}

fn checksums(input: [u8; 2]) -> Vec<u16>
    resources peak(memory) <= 600,
{
    let blocks: &[u8] = &input;
    let mut sums = Vec::with_capacity(2);

    // One decoded block, the checksum helper's allowance, and up to 48 bytes
    // for the iterator, yielded reference, and expression temporaries.
    resources peak(memory) <= value_size(Block) + peak(checksum) + 48 {
        for block in blocks {
            let decoded = [*block; 64];
            sums.push(checksum(&decoded));
        }
    }
    sums
}

} // verus!

fn main() {
    assert_eq!(checksums([1, 2]), vec![64, 128]);
}
