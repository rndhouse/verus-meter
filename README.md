# Verus Meter

Verus Meter is an experimental fork of [Verus](https://github.com/verus-lang/verus)
that adds resource contracts for Rust. It currently supports proofs of upper bounds
on algorithmic memory use for a subset of Rust.

## Why

- Prove peak memory bounds across all permitted inputs.
- Verify that memory guarantees remain valid as code changes.
- Verify memory bounds across function calls and nested operations.
- Support input-dependent and execution-path-specific memory budgets.

## Examples

A simple example:

```rust
// Reverse a small buffer using either a copy or a sequence of swaps.
//
// The caller keeps paying for the borrowed array; mem_size(values) counts
// only the reference. The `if` lets us specify a different memory bound for
// each reversal strategy.
fn reverse(values: &mut [u32; 4], use_scratch: bool)
    mem_peak <= mem_size(values) + mem_size(use_scratch) + if use_scratch {
        mem_size([u32; 4])
    } else {
        mem_size(u32)
    },
{
    if use_scratch {
        let copy = *values;
        values[0] = copy[3];
        values[1] = copy[2];
        values[2] = copy[1];
        values[3] = copy[0];
    } else {
        let mut saved = values[0];
        values[0] = values[3];
        values[3] = saved;
        saved = values[1];
        values[1] = values[2];
        values[2] = saved;
    }
}

// Reverse two buffers using the memory needed for just one reversal.
fn main()
    mem_peak <= mem_size([u32; 4]) + mem_peak(reverse),
{
    {
        let mut first = [1u32, 2, 3, 4];
        reverse(&mut first, false);
    }
    {
        let mut second = [5u32, 6, 7, 8];
        reverse(&mut second, true);
    }
}
```

Each strategy must fit its own allowance in the conditional budget. The caller
uses `mem_peak(reverse)` to allow for either strategy. Separate scopes let both
reversals share one overall budget; keeping both buffers alive would exceed it
and fail verification.

Bounds describe a source-level model, not the compiled program’s actual memory use.

- [Examples](examples/resource/memory): complete programs with explanatory comments.
  - [Reusing workspace](examples/resource/memory/storage.rs): share a memory allowance across scopes, branches, and loops.
  - [Calling helpers](examples/resource/memory/calls.rs): combine a caller's data with a helper's memory needs.
  - [Checkpoints](examples/resource/memory/checkpoints.rs): check the peak reached at individual stages of an operation.
  - [Sections](examples/resource/memory/sections.rs): divide a larger operation into independently budgeted pieces.
  - [Conditional budgets](examples/resource/memory/conditional.rs): give different inputs different memory allowances.
  - [Budgets across calls](examples/resource/memory/call_budgets.rs): preserve those input-specific allowances through a chain of helpers.
  - [Returning buffers](examples/resource/memory/returns.rs): hand a buffer to its caller without counting its storage twice.
  - [Heap buffers](examples/resource/memory/heap.rs): reuse a heap allowance by releasing each buffer before creating the next.
  - [Nested ownership](examples/resource/memory/nested_ownership.rs): compose boxes, vectors, and structs while counting each allocation once.
  - [Nested growth](examples/resource/memory/nested_growth.rs): grow individual vector fields and preserve their allocation effects through helpers.
  - [Owning collections](examples/resource/memory/owning_collections.rs): account for runtime collections of children that own further allocations.
  - [Boxed slices](examples/resource/memory/boxed_slices.rs): convert vectors into fixed-length owning slices and transfer their storage.
  - [Ownership](examples/resource/memory/ownership.rs): track an allocation's cost as it passes between helpers.
  - [Vectors](examples/resource/memory/vectors.rs): collect values while proving that every addition fits the reserved capacity.
  - [Growing vectors](examples/resource/memory/vector_growth.rs): budget for replacement buffers and retained allocations across helper calls.
  - [Borrowing vectors](examples/resource/memory/vector_helpers.rs): let helpers use a vector within its existing reservation.
  - [Returning vectors](examples/resource/memory/vector_returns.rs): create a reserved buffer in a helper and use it in the caller.
  - [Optional results](examples/resource/memory/options.rs): keep a result after releasing the collection that held it.
  - [Integer types](examples/resource/memory/integers.rs): adjust a counter while checking arithmetic safety and memory use.
  - [Insertion sort](examples/resource/memory/insertion_sort.rs): prove sorting correctness with workspace that stays fixed as inputs grow.
  - [Structs](examples/resource/memory/structs.rs): sort data inside a struct while budgeting for both the data and the sorting work.
  - [Deliberate violations](examples/resource/memory/expected-failures): see verification reject unbudgeted copies, overlapping allocations, and vector growth.

## Docs

- [Memory contracts](docs/verus-meter/model.md): how to write and understand the guarantees.
