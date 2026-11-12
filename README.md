# Verus Meter

Verus Meter is an experimental fork of [Verus](https://github.com/verus-lang/verus)
that adds resource contracts for Rust. It currently supports proofs of upper bounds
on algorithmic memory use for a subset of Rust.

## Why

- Prove peak memory bounds across all permitted inputs.
- Verify that memory guarantees remain valid as code changes.
- Verify memory bounds across function calls and nested operations.
- Support input-dependent and execution-path-specific memory budgets.

## An Example

This [example](examples/resource/memory/heap/loops/buffer_collection.rs) copies a
local array into one heap buffer per iteration. The same `count` input determines
both the number of iterations and the memory budget:

```rust
type Buffer = [u8; 16];

// Cover the local array, collection, input and counter, all retained buffers,
// and the pending box handle before it moves into the collection.
spec fn collection_budget(count: u16) -> nat {
    let backing = (count as nat) * value_size(Box<Buffer>);
    let allocations = (count as nat) * value_size(Buffer);

    // The local source array, count input, loop counter, and pending box handle
    // before it moves into the collection. Heap payloads are counted above.
    let temporary = value_size(Buffer) + value_size(count) + value_size(u16)
        + value_size(Box<Buffer>);

    value_size(Vec<Box<Buffer>>) + backing + allocations + temporary
}

// Return one independently allocated copy of the local array per iteration.
fn collect_buffers(count: u16) -> Vec<Box<Buffer>>
    resources peak(memory) <= collection_budget(count),
{
    let local = [7u8; 16];
    let mut buffers = Vec::with_capacity(count as usize);
    let mut iteration = 0u16;
    while iteration < count {
        let buffer = Box::new(local);
        buffers.push(buffer);
        iteration += 1;
    }
    buffers
}
```

The memory budget grows with `count`. Verus checks that it holds for every `u16`
`count`, including zero.

If we allocate an extra box after each push, it overlaps the retained buffers:

```rust
buffers.push(buffer);
let extra = Box::new(local); // Not covered by the declared budget.
```

Run the [failing version](examples/resource/memory/expected-failures/heap_overlap.rs)
from the repository root, after [building Verus](BUILD.md):

```console
$ VERUS_Z3_PATH="$PWD/source/z3" ./source/target-verus/release/verus examples/resource/memory/expected-failures/heap_overlap.rs
error: conditional memory budget exceeded: cannot prove the required model bytes fit the declared bound
  --> examples/resource/memory/expected-failures/heap_overlap.rs:35:21
   |
26 |     resources peak(memory) <= collection_budget(count),
   |                               ------------------------
...
35 |         let extra = Box::new(local);
   |                     ^^^^^^^^^^^^^^^

verification results:: 2 verified, 1 errors
error: aborting due to 1 previous error
```

## More Examples

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
