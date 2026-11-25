// This example shows how a caller can keep a result after a helper releases the vector
// that held it.
//
// The peak covers the vector, its reserved slots, and the optional result. The caller
// can then use that result within the same allowance.

use vstd::prelude::*;

verus! {

/// `last_number` pops the last number and returns it as an `Option`.
///
/// The allowance covers the vector, its two reserved elements, and the optional
/// result. Functional verification proves that this collection provides a number.
fn last_number() -> (result: Option<u32>)
    ensures result == Some(20),
    resources peak(memory) <= value_size(Vec<u32>) + 2 * value_size(u32) + value_size(Option<u32>),
{
    let mut numbers = Vec::<u32>::with_capacity(2);
    numbers.push(10);
    numbers.push(20);
    numbers.pop()
}

/// `main` uses the returned number after the helper's vector goes out of scope.
///
/// The helper's guarantee proves that this call supplies a number. Its memory
/// allowance also covers using the result after the collection is gone.
fn main()
    resources peak(memory) <= peak(last_number),
{
    let result = last_number();
    match result {
        Some(number) => { assert(number == 20); }
        None => { assert(false); }
    }
}

}
