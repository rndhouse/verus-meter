# 4. Indexed traversal and updates

Builds on tasks [1](complete/01-compose-iteration-operations.md) through
[3](complete/03-transform-children.md). Incoming ownership is completed in
[task 5](05-borrowed-and-incoming-ownership.md).

## Goal

Describe repeated ownership operations at runtime-selected child paths, including
indexed mutation, replacement, and removal with reindexing.

## Current restriction

Loop summaries support last-element removal but not general indexed removal or
updates beneath runtime indices. Persistent collection roles must use fixed
paths. Repeatedly popping, changing, and restoring the last child also needs a
repeated-visit transformation rather than a traversal into a disjoint destination.
Incoming-child indexing has an additional explicit loop guard, even for
some reads; that lifetime boundary also requires task 5.

## Work

- [ ] Extend iteration effects to runtime-selected paths using shared forest
  selection, partition, replacement, and reindexing operations.
- [ ] Define how successive indices relate to the evolving collection, including
  repeated visits and index shifts after removal.
- [ ] Compose indexed child loans and updates with the transformations from task 3.
- [ ] Preserve untouched children, nested fixed fields, and reservation facts.
- [ ] Define representable index dependencies and reject unsupported aliasing or
  access patterns. Separate path algebra from incoming-lifetime restrictions so
  task 5 can reuse it.

## Completion criteria

Tests cover repeated updates to the same child, traversal of distinct children,
removal with shifted indices, and nested runtime paths. Subsequent caller
extraction distinguishes modified and untouched children. Replacement checks
include the period when both old and new allocations are live. Document the
remaining incoming-owner boundary until task 5 completes it.

## Starting points

- [Indexed loans](../../../../source/vir/src/resource/memory/projections.rs)
- [Shared forest operations](../../../../source/vir/src/resource/memory/metadata/operations.rs)
- [Iteration path restrictions](../../../../source/vir/src/resource/memory/transfer/trace/loops.rs)
- [Element transfer tests](../../../../source/rust_verify_test/tests/resource/memory/element_transfers.rs)
- [Incoming child tests](../../../../source/rust_verify_test/tests/resource/memory/incoming_children.rs)
