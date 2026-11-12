# 7. Other loop forms and early exits

Builds on tasks [1](complete/01-compose-iteration-operations.md) through
[6](complete/06-iteration-counts-and-state.md). This also touches general resource
control flow, beyond collection ownership summaries.

## Goal

Reuse the checked loop model for additional source loop forms and explicitly
account for ownership and peak usage on every exit edge.

## Current restriction

Resource checking admits supported condition-bearing, unit-valued while loops.
`for`/iterator loops, unconditional `loop`, and explicit `break`, `continue`, or
`return` remain unsupported. These require more than changing summary recognition:
body accounting must handle scope cleanup, back edges, and exits.

## Work

- [ ] Represent normal completion, continuation, break, and function return with
  their live ownership and allocation lifetimes.
- [ ] Preserve scope cleanup and peak history on every edge, including nested and
  labelled exits and interaction with budgeted memory sections.
- [ ] Admit unconditional loops and value-producing breaks where the exit
  transformation is representable.
- [ ] Integrate supported `for` forms with the existing Verus lowering and shared
  iteration model, accounting for iterator state and any owned storage.
- [ ] Define supported iterator classes and adapters explicitly. Iterator or
  container behavior without an ownership model must still reject.
- [ ] Check frontend, macro, and verification boundaries according to the
  integration guide; do not build a parallel loop accounting implementation.

## Completion criteria

Tests cover early termination, skipped iterations, nested exits, returned owning
values, and cleanup of temporary allocations. Equivalent supported while and
for traversals preserve caller-visible ownership and peak bounds. Unsupported
iterator classes and exit dependencies have explicit rejection tests. Document
the resulting source subset rather than claiming support for all iterators.

## Starting points

- [Loop admission](../../../../source/vir/src/resource/memory/loops.rs)
- [Body proof driver](../../../../source/vir/src/resource/memory/loops/analysis.rs)
- [Expression accounting](../../../../source/vir/src/resource/memory/analysis.rs)
- [Storage and exit tests](../../../../source/rust_verify_test/tests/resource/memory/storage.rs)
- [Loop checkpoint tests](../../../../source/rust_verify_test/tests/resource/memory/checkpoints.rs)
- [Integration boundaries](../../integration.md)
