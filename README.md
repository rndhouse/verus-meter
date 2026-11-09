# Verus Meter

Verus Meter is an experimental fork of [Verus](https://github.com/verus-lang/verus)
that adds resource contracts for Rust. A function declares a workspace budget,
and verification catches changes that exceed it alongside checking functional
correctness.

```rust
// Reverse a small buffer using a temporary copy.
//
// Borrowing keeps the original array charged to the caller; mem_size(values)
// counts only the reference. The temporary copy needs a separate array.
fn reverse(values: &mut [u32; 4])
    mem_peak <= mem_size(values) + mem_size([u32; 4]),
{
    let copy = *values;
    values[0] = copy[3];
    values[1] = copy[2];
    values[2] = copy[1];
    values[3] = copy[0];
}

// Reverse two buffers using the memory needed for just one reversal.
fn main()
    mem_peak <= mem_size([u32; 4]) + mem_peak(reverse),
{
    {
        let mut first = [1u32, 2, 3, 4];
        reverse(&mut first);
    }
    {
        let mut second = [5u32, 6, 7, 8];
        reverse(&mut second);
    }
}
```

The caller's budget covers one buffer plus the helper's declared memory needs.
Each scope releases its buffer before the next begins. Removing the inner scopes
keeps both buffers live during the second call, exceeding the same budget.
The verifier accounts for storage automatically; contracts add no runtime tracking.

Functions can refer to helper functions' budgets, divide work into independently
checked sections, and check the peak reached at a particular point. Conditional
contracts can give different inputs different allowances and preserve them through
helper calls. Boxes and vectors without growth can also carry checked
heap allowances; vector budgets can scale with a runtime capacity. Helpers can
return values, including `Option`, with result storage counted once across the call.
Heap ownership can pass between helpers; moving a value into the result transfers
its charge, and allocations remain charged until their new owner releases them.

Bounds describe declared storage and supported heap objects under a fixed memory
model. Physical stack size and allocator overhead are outside the guarantee.
Support is limited to a subset of Rust; unsupported operations are rejected in
checked functions.

- [Memory contracts](docs/verus-meter/model.md): how to write and understand the guarantees.
- [Examples](examples/resource/memory): complete programs with explanatory comments.
- [A deliberate violation](examples/resource/memory/expected-failures/array_copy.rs):
  an extra copy that makes verification fail.

The [memory verifier tests](source/rust_verify_test/tests/resource/memory)
run together from `source/`:

```sh
cargo test --release -p rust_verify_test --test resource memory:: -- --test-threads=2
```

Replace `memory::` with a topic such as `memory::ownership::` to select one suite.
