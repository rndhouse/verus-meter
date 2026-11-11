# 1. Compose iteration operations

## Goal

Represent a checked iteration as a composable ownership transformation. Direct
operations, helper effects, and completed inner loops should use the same
composition rules.

## Supported boundary

A checked iteration composes ordered operations into monotone blocks on disjoint
persistent collection roles: fresh appends, last-element removals, and contiguous
whole-child transfers to one destination in extraction order. Exact extraction
and restoration sequences reduce to identity. Direct operations, precise helper
programs, and completed nested counted loops use the same composition rules.

Fixed owner roles stay stable. Runtime-indexed roles, conditional effects, changed
payloads, permutations, partial routing of an extracted range, and mixed growth
and removal on one role remain unsupported. Borrowed incoming traversal and new
count forms belong to the later tasks. Existing lifetime-protection checks remain
in force for enclosing owners and overlapping paths.

## Work

- [x] Reduce ordered whole-child extraction/restoration to identity effects,
  propagate those effects through nested loops, and prove preservation of child
  charges and backing while retaining intermediate peak checks.
- [x] Define ordered composition over checked ownership effects, including
  dependencies and overlapping paths. Validate representability before exporting
  a repeated transformation.
- [x] Support multiple unconditional operations on one persistent collection,
  including extraction followed by reinsertion, without losing child identity or
  counting an allocation twice.
- [x] Preserve enough effect information through helper calls and inner loop
  summaries for the outer iteration to consume it through the same mechanism.
- [x] Keep input-region transitions and local conservation proofs consistent with
  the composed transformation, including intermediate allocation peaks.
- [x] State the remaining restrictions on changing persistent owner roles. Do not
  simply remove lifetime-protection checks to admit overlapping effects.

## Completion criteria

Equivalent supported operations written directly, factored into a helper, or
grouped in a nested counted loop produce consistent caller-visible ownership.
Tests cover repeated operations on one collection, unchanged sibling ownership,
zero iterations, retained storage, and peak overlap. Unsupported dependencies
continue to reject. Initial composition can retain the existing count forms and
unconditional effects; later tasks extend those dimensions.

The regression boundary includes multiple-operation blocks, helpers that insert
or forward unchanged whole arguments, nested block repetition, fixed sibling
roles, exact caller extraction, original-input lifetimes, and zero/partial/full
iteration ranges. Negative checks cover insufficient budgets, changing inner
counts, reordered or partially routed ranges, changed helper payloads, and
allocation overlap that appears only on later iterations.

## Starting points

- [Iteration analysis](../../../../../source/vir/src/resource/memory/transfer/trace/loops.rs)
- [Ordered effect composition](../../../../../source/vir/src/resource/memory/transfer/trace/loops/composition.rs)
- [Checked operation adapters](../../../../../source/vir/src/resource/memory/transfer/trace/operations.rs)
- [Shared loop records](../../../../../source/vir/src/resource/memory/loops.rs)
- [Loop ownership tests](../../../../../source/rust_verify_test/tests/resource/memory/loop_ownership.rs)
- [Helper control-flow tests](../../../../../source/rust_verify_test/tests/resource/memory/helper_control.rs)
