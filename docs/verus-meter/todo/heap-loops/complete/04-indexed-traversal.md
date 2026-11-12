# 4. Indexed traversal and updates

Builds on tasks [1](01-compose-iteration-operations.md) through
[3](03-transform-children.md). Incoming ownership is completed in
[task 5](05-borrowed-and-incoming-ownership.md).

## Goal

Describe repeated ownership operations at runtime-selected child paths, including
indexed mutation, replacement, and removal with reindexing.

## Supported boundary

Ordered recurrences apply the checked body to the previous visit's complete
forest. Selection, replacement, partitioning, and removal with reindexing share
the straight-line ownership algebra. Repeated visits, distinct indices, nested
runtime/fixed paths, and pop/change/restore therefore compose without separate
rules for particular container nesting shapes. Source bounds and overflow checks
remain ordinary executable obligations.

Indexed loans can call precise leaf helpers, including helpers whose own loops
produce complete recurrences. Each changed borrowed parameter is published to
the caller. Untouched children retain their descriptors; affected uniform
reservation candidates are weakened before replacement. Read-only loans restore
the saved forest directly. Byte induction includes backing storage and children,
and replacement keeps old/new overlap charged.

Counts retain the existing unit-counter and unit-consumption forms. Their bound
observations must be stable for a parametric iteration. Pure scalar arithmetic
and representable metadata observations can select indices; unsupported payload
values, additional persistent scalar writes, or effects during index evaluation
reject. Exact finite normalization assists small counts. Broader symbolic cost
and view induction remains in [task 6](../06-iteration-counts-and-state.md).

Indexed incoming children, borrowed incoming extraction in loops, and incoming
runtime-helper delegation are covered by [task 5](05-borrowed-and-incoming-ownership.md).
The path algebra is independent of those lifetime restrictions.

## Work

- [x] Extend iteration effects to runtime-selected paths using shared forest
  selection, partition, replacement, and reindexing operations.
- [x] Define how successive indices relate to the evolving collection, including
  repeated visits and index shifts after removal.
- [x] Compose indexed child loans and updates with the transformations from task 3.
- [x] Preserve untouched children, nested fixed fields, and reservation facts.
- [x] Define representable index dependencies and reject unsupported aliasing or
  access patterns. Separate path algebra from incoming-lifetime restrictions so
  task 5 can reuse it.

## Completion criteria

Tests cover repeated updates to the same child, traversal of distinct children,
removal with shifted indices, and nested runtime paths. Subsequent caller
extraction distinguishes modified and untouched children. Replacement checks
include the period when both old and new allocations are live. Document the
remaining incoming-owner boundary until task 5 completes it.

## Starting points

- [Indexed loans](../../../../../source/vir/src/resource/memory/projections.rs)
- [Shared forest operations](../../../../../source/vir/src/resource/memory/metadata/operations.rs)
- [Iteration path restrictions](../../../../../source/vir/src/resource/memory/transfer/trace/loops.rs)
- [Element transfer tests](../../../../../source/rust_verify_test/tests/resource/memory/element_transfers.rs)
- [Incoming child tests](../../../../../source/rust_verify_test/tests/resource/memory/incoming_children.rs)
- [Indexed loop regressions](../../../../../source/rust_verify_test/tests/resource/memory/indexed_loops.rs)
