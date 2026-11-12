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
// The caller keeps paying for the borrowed array. The `if` lets us specify
// a different memory bound for each reversal strategy.
fn reverse(values: &mut [u32; 4], use_scratch: bool)
    resources peak(memory) <= ref_size(values) + value_size(use_scratch) + if use_scratch {
        value_size([u32; 4])
    } else {
        value_size(u32)
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
    resources peak(memory) <= value_size([u32; 4]) + peak(reverse),
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
uses `peak(reverse)` to allow for either strategy. Separate scopes let both
reversals share one overall budget; keeping both buffers alive would exceed it
and fail verification.

Bounds describe a source-level model, not the compiled program’s actual memory use.

Explore the [memory examples](examples/resource/memory/README.md):

- **Basics:** [Scopes, values, and returned buffers](examples/resource/memory/README.md#basics).
- **Contracts:** [Budgets, formulas, sections, and checkpoints](examples/resource/memory/README.md#contracts).
- **Heap:** [Allocations and ownership transfers](examples/resource/memory/README.md#heap).
- **Heap loops:** [Construction, transfers, and allocation overlap](examples/resource/memory/README.md#loops).
- **Vectors:** [Capacity, growth, and owning elements](examples/resource/memory/README.md#vectors).
- **Algorithms:** [Sorting within a memory budget](examples/resource/memory/README.md#algorithms).
- **Deliberate violations:** [Examples that exceed their allowances](examples/resource/memory/README.md#deliberate-violations).

## Docs

- [Memory contracts](docs/verus-meter/model.md): how to write and understand the guarantees.
