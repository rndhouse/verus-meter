# 8. For loops and iterator state

Builds on [task 7](complete/07-loop-forms-and-exits.md), which supplies checked exit edges,
scope cleanup, and unconditional-loop accounting.

## Goal

Integrate supported `for` forms with the existing Verus lowering and shared
iteration model, accounting for iterator state and any owned storage.

## Work

- [ ] Define supported iterator classes and adapters explicitly. Iterator or
  container behavior without an ownership model must still reject.
- [ ] Recognize supported operations by compiler identity and reuse existing
  Verus lowering; do not create another loop accounting implementation.
- [ ] Account for iterator initialization, advancement, exhaustion, temporary
  results, and storage retained by the iterator.
- [ ] Compose precise iteration effects with task 7's break, continue, return,
  and nested or labelled exit cleanup.
- [ ] Check frontend, macro, erasure, and verification boundaries according to
  the integration guide.

## Completion criteria

Equivalent supported while and for traversals preserve caller-visible ownership
and peak bounds, with iterator storage charged separately. Tests cover empty
traversals, exhaustion, early exits, and any admitted owning iterators or adapters.
Unsupported classes and adapters have explicit rejection tests. Document the
resulting source subset rather than claiming support for all iterators.

## Starting points

- [Existing for lowering](../../../../source/builtin_macros/src/syntax.rs)
- [Iterator specifications and wrapper](../../../../source/vstd/std_specs/iter.rs)
- [Loop admission](../../../../source/vir/src/resource/memory/loops.rs)
- [Compiler operation identities](../../../../source/rust_verify/src/resource/memory/intrinsics.rs)
- [Integration boundaries](../../integration.md)
