// Decode and checksum each input byte as a run of BLOCK_BYTES identical bytes.

use vstd::prelude::*;

verus! {

const BLOCK_BYTES: usize = 128;
type Block = [u8; BLOCK_BYTES];

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

fn checksums(input: [u8; 2]) -> Vec<u16>
    resources peak(memory) <= value_size(input) + ref_size(&[u8]) + value_size(Vec<u16>) + 937,
{
    let packed: &[u8] = &input;
    let mut sums = Vec::new();

    // Both decoded blocks occupy reserved slots while the checksums are produced.
    resources peak(memory) <= 937 {
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
