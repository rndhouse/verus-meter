# 1. Compose iteration operations

## Goal

Represent a checked iteration as a composable ownership transformation. Direct
operations, helper effects, and completed inner loops should use the same
composition rules.

## Current restriction

The summarizer accepts one unconditional append or pop per disjoint persistent
collection after ordered whole-child restoration sequences have been reduced.
Other multiple operations on the same collection and overlapping paths reject.
Helper mutations and nonidentity inner loops that change an outer collection do not
generally expose effects that the enclosing iteration can compose. Fixed owner
roles must remain stable; moving or dropping an enclosing owner is also guarded.

## Work

- [x] Reduce ordered whole-child extraction/restoration to identity effects,
  propagate those effects through nested loops, and prove preservation of child
  charges and backing while retaining intermediate peak checks.
- [ ] Define ordered composition over checked ownership effects, including
  dependencies and overlapping paths. Validate representability before exporting
  a repeated transformation.
- [ ] Support multiple unconditional operations on one persistent collection,
  including extraction followed by reinsertion, without losing child identity or
  counting an allocation twice.
- [ ] Preserve enough effect information through helper calls and inner loop
  summaries for the outer iteration to consume it through the same mechanism.
- [ ] Keep input-region transitions and local conservation proofs consistent with
  the composed transformation, including intermediate allocation peaks.
- [ ] State the remaining restrictions on changing persistent owner roles. Do not
  simply remove lifetime-protection checks to admit overlapping effects.

## Completion criteria

Equivalent supported operations written directly, factored into a helper, or
grouped in a nested counted loop produce consistent caller-visible ownership.
Tests cover repeated operations on one collection, unchanged sibling ownership,
zero iterations, retained storage, and peak overlap. Unsupported dependencies
continue to reject. Initial composition can retain the existing count forms and
unconditional effects; later tasks extend those dimensions.

This task remains open until nonidentity operation sequences and helper effects
meet the criteria above. Identity reduction alone does not complete task 1.

## Starting points

- [Iteration analysis](../../../../source/vir/src/resource/memory/transfer/trace/loops.rs)
- [Ordered effect composition](../../../../source/vir/src/resource/memory/transfer/trace/loops/composition.rs)
- [Checked operation adapters](../../../../source/vir/src/resource/memory/transfer/trace/operations.rs)
- [Shared loop records](../../../../source/vir/src/resource/memory/loops.rs)
- [Loop ownership tests](../../../../source/rust_verify_test/tests/resource/memory/loop_ownership.rs)
- [Helper control-flow tests](../../../../source/rust_verify_test/tests/resource/memory/helper_control.rs)
