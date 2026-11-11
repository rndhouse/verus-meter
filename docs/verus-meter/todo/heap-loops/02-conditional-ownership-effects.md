# 2. Conditional ownership effects

Depends on [task 1](01-compose-iteration-operations.md).

## Goal

Compose branch-dependent ownership changes across iterations while preserving
the relationship between the branch decision and the resulting allocations.

## Current restriction

Collection loop summaries require unconditional effects. Conditional appends,
removals, and transfers between alternative destinations cannot generally be
summarized, even though ordinary branches work in other contexts.

## Work

- [ ] Represent guarded iteration effects and ownership joins using the shared
  composition mechanism.
- [ ] Distinguish an iteration-invariant condition from a condition that varies
  with the iteration or payload. Define which predicates can be summarized and
  how their selection counts and child ordering are represented.
- [ ] Handle conditional insertion/removal and routing a whole child to one of
  multiple destinations without assuming that every branch executes.
- [ ] Preserve allocation lifetimes and peak checks on each path, including
  branches that leave ownership unchanged.

## Completion criteria

Tests exercise no selected iterations, all selected iterations, mixed selections,
and alternative destinations. Caller extraction observes the correct surviving
children and order. Excess usage fails verification; unrepresentable predicates
reject rather than producing a guessed aggregate footprint. Document any
remaining predicate restrictions explicitly.

## Starting points

- [Iteration analysis](../../../../source/vir/src/resource/memory/transfer/trace/loops.rs)
- [Ownership evaluator](../../../../source/vir/src/resource/memory/transfer/trace.rs)
- [Conditional loop rejection](../../../../source/rust_verify_test/tests/resource/memory/helper_control.rs)
- [Loop dependency regressions](../../../../source/rust_verify_test/tests/resource/memory/loop_ownership.rs)
