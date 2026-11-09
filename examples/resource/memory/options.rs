// Extract a number from a temporary collection and use it after the collection is gone.
//
// Option lets the result describe whether a number was available. The vector's
// reservation ends inside the helper, while the returned value stays with its caller.

use vstd::prelude::*;

verus! {

// Keep the last number while releasing the collection that held it.
//
// The allowance covers the vector, its reserved elements, and the optional
// result. Functional verification proves that this collection provides a number.
fn last_number() -> (result: Option<u32>)
    ensures result == Some(20),
    mem_peak <= mem_size(Vec<u32>) + 2 * mem_size(u32) + mem_size(Option<u32>),
{
    let mut numbers = Vec::<u32>::with_capacity(2);
    numbers.push(10);
    numbers.push(20);
    numbers.pop()
}

// Use the returned number without retaining the collection's heap storage.
//
// The helper's guarantee proves that this call supplies a number. Its memory
// allowance also covers using the result after the collection is gone.
fn main()
    mem_peak <= mem_peak(last_number),
{
    let result = last_number();
    match result {
        Some(number) => { assert(number == 20); }
        None => { assert(false); }
    }
}

}
