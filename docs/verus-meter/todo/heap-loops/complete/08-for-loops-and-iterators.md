# 8. For loops and iterator state

Builds on [task 7](07-loop-forms-and-exits.md), which supplies checked exit edges,
scope cleanup, and unconditional-loop accounting.

## Goal

Integrate supported `for` forms with the existing Verus lowering and shared
iteration model, accounting for iterator state and any owned storage.

## Supported boundary

Finite half-open ranges over native integers and the standard `rev`, `skip`, and
`take` adapters use exact scalar sequence descriptions. Compositions retain
their native inline state, selection, and order; ghost wrapper fields are erased.
Aliases and named local iterators retain the same compiler identities. A discarded
scalar item needs no named slot. Checked factories preserve scalar iterator state
through calls, including constructor evaluation order. Borrowed and owning element
iterators, inclusive ranges, other adapters, and missing iterator-state inference
remain unsupported.

The existing Verus lowering and shared checked loop records supply successful
visits, exhaustion edges, and ordinary count proofs. Nested queries use the
containing loop's pre-advance snapshot. Continuations, single-visit breaks,
returns, labelled exits, and section cleanup reuse task 7's lifetime rules.
Partial exits without an exact stopping transformation cannot export runtime
ownership summaries. Standard generated iterator invariants remain required.

## Work

- [x] Define supported iterator classes and adapters explicitly. Iterator or
  container behavior without an ownership model must still reject.
- [x] Recognize supported operations by compiler identity and reuse existing
  Verus lowering; do not create another loop accounting implementation.
- [x] Account for iterator initialization, advancement, exhaustion, temporary
  results, and storage retained by the iterator.
- [x] Compose precise iteration effects with task 7's break, continue, return,
  and nested or labelled exit cleanup.
- [x] Check frontend, macro, erasure, and verification boundaries according to
  the integration guide.

## Completion criteria

Equivalent supported while and for traversals preserve caller-visible ownership
and peak bounds, with iterator storage charged separately. Tests cover empty
traversals, exhaustion, early exits, and any admitted owning iterators or adapters.
Unsupported classes and adapters have explicit rejection tests. Document the
resulting source subset rather than claiming support for all iterators.

## Starting points

- [Existing for lowering](../../../../../source/builtin_macros/src/syntax.rs)
- [Iterator specifications and wrapper](../../../../../source/vstd/std_specs/iter.rs)
- [Loop admission](../../../../../source/vir/src/resource/memory/loops.rs)
- [Compiler operation identities](../../../../../source/rust_verify/src/resource/memory/intrinsics.rs)
- [Iterator layouts and operations](../../../../../source/vir/src/resource/memory/iterators.rs)
- [For-loop adaptation](../../../../../source/vir/src/resource/memory/for_loops.rs)
- [Iterator regressions](../../../../../source/rust_verify_test/tests/resource/memory/for_loops.rs)
- [Integration boundaries](../../../integration.md)
