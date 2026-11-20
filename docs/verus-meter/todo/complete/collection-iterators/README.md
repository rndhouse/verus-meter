# Collection iterators

Support `for block in blocks` in resource-checked Rust when the loop borrows a
slice or vector, or consumes a vector. The [range iterator work](../heap-loops/complete/08-for-loops-and-iterators.md)
already handles loop lowering, progress and exits. These tasks add the memory
effects of yielding a reference or transferring an owned element.

- [x] [01 — Borrowed slices and vectors](complete/01-borrowed-iteration.md)
- [x] [02 — Consuming vectors](complete/02-consuming-vectors.md)

## Acceptance example

Use the same input, checksum operation and output collection in both versions.
Start with at least two blocks whose decoded buffers can coexist in the staged
version. Keep one fixed section budget around the entire traversal.

1. Stream the input with `for block in blocks`, where `blocks` is a shared
   slice. Decode, checksum and drop each buffer within one iteration. Derive a
   section allowance that covers this version and verify it.
2. Stage the decoded buffers in a vector, then consume it with
   `for decoded in staged` to produce the checksums in the same order. Keep
   both loops and the staging vector inside the section. The original allowance
   must fail with a memory-budget diagnostic.
3. Raise only the section allowance and verify the staged version. This
   distinguishes a genuine peak regression from an unsupported iterator or an
   unproved indexing obligation. Size the enclosing function budget to admit
   both section allowances.

Use ordinary collection loops in the example, with no handwritten loop
invariants for memory accounting. Functional properties such as checksum
arithmetic can still require their own proofs. Record the passing example and
its expected failure in the [memory examples](../../../../../examples/resource/memory/README.md)
and update the [supported boundary](../../../../model.md) as each form lands.

Mutable iteration, by-value arrays, arbitrary iterator implementations and
additional adapters can be scoped separately.
