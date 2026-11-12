# 5. Borrowed collections and incoming ownership

Builds on tasks [1](complete/01-compose-iteration-operations.md) through
[4](complete/04-indexed-traversal.md).

## Goal

Apply the supported loop transformations to collections supplied by callers,
whether moved into the function or borrowed, and preserve that support through
helper delegation.

## Current restriction

Existing by-value inputs support consuming transformations, transfers, and
indexed removals at the collection root.
Extraction through borrowed incoming collections remains blocked in loops.
Indexed incoming children and indexed replacement in owned inputs also have
loop restrictions. Forwarding incoming runtime ownership to another helper can
fail because the call path requires complete local argument metadata.

## Work

- [ ] Carry precise caller-supplied ownership descriptors through supported loop
  operations without treating zero local charge as an empty incoming allocation.
- [ ] Support repeated extraction and indexed updates through borrowed inputs,
  preserving the caller's remainder and any transferred results.
- [ ] Compose incoming ownership through helper calls using the same operation
  model as direct execution.
- [ ] Keep original allocation lifetimes separate from allocations created by the
  callee and update caller ownership exactly once after the call.
- [ ] Replace protection guards only where a checked lifetime transition now
  justifies the operation. Preserve unrelated branch and memory-section limits.

## Completion criteria

Tests compare supported direct and delegated operations for owned and borrowed
inputs, including empty collections, partial traversal, nested children, and
caller use after the call. Caller budgets account for surviving and extracted
allocations independently. No copied parent charge or aggregate ownership
fallback is introduced.

## Starting points

- [Indexed incoming guard](../../../../source/vir/src/resource/memory/projections.rs)
- [Helper argument eligibility](../../../../source/vir/src/resource/memory/transfer/calls.rs)
- [Heap protection and partitioning](../../../../source/vir/src/resource/memory/heap.rs)
- [Input lifetime regions](../../../../source/vir/src/resource/memory/provenance.rs)
- [Incoming extraction tests](../../../../source/rust_verify_test/tests/resource/memory/incoming_extraction.rs)
- [Incoming child tests](../../../../source/rust_verify_test/tests/resource/memory/incoming_children.rs)
