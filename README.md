# Verus Meter

Verus Meter is an experimental fork of [Verus](https://github.com/verus-lang/verus)
that adds resource contracts for Rust. You can prove that your code produces
the right results and stays within its memory budget.

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
  - [Reusing workspace](examples/resource/memory/storage.rs): share a memory allowance across scopes, branches, and loops.
  - [Calling helpers](examples/resource/memory/calls.rs): combine a caller's data with a helper's memory needs.
  - [Checkpoints](examples/resource/memory/checkpoints.rs): check the peak reached at individual stages of an operation.
  - [Sections](examples/resource/memory/sections.rs): divide a larger operation into independently budgeted pieces.
  - [Conditional budgets](examples/resource/memory/conditional.rs): give different inputs different memory allowances.
  - [Budgets across calls](examples/resource/memory/call_budgets.rs): preserve those input-specific allowances through a chain of helpers.
  - [Returning buffers](examples/resource/memory/returns.rs): hand a buffer to its caller without counting its storage twice.
  - [Heap buffers](examples/resource/memory/heap.rs): reuse a heap allowance by releasing each buffer before creating the next.
  - [Ownership](examples/resource/memory/ownership.rs): track an allocation's cost as it passes between helpers.
  - [Vectors](examples/resource/memory/vectors.rs): collect values while proving that every addition fits the reserved capacity.
  - [Borrowing vectors](examples/resource/memory/vector_helpers.rs): let helpers use a vector within its existing reservation.
  - [Returning vectors](examples/resource/memory/vector_returns.rs): create a reserved buffer in a helper and use it in the caller.
  - [Optional results](examples/resource/memory/options.rs): keep a result after releasing the collection that held it.
  - [Integer types](examples/resource/memory/integers.rs): adjust a counter while checking arithmetic safety and memory use.
  - [Insertion sort](examples/resource/memory/insertion_sort.rs): prove sorting correctness with workspace that stays fixed as inputs grow.
  - [Structs](examples/resource/memory/structs.rs): sort data inside a struct while budgeting for both the data and the sorting work.
  - [Deliberate violations](examples/resource/memory/expected-failures): see verification reject extra copies, overlapping allocations, and vector growth.

The [memory verifier tests](source/rust_verify_test/tests/resource/memory)
run together from `source/`:

```sh
cargo test --release -p rust_verify_test --test resource memory:: -- --test-threads=2
```

Replace `memory::` with a topic such as `memory::ownership::` to select one suite.
