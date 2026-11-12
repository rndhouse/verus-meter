# 7. Loop exits and unconditional loops

Builds on tasks [1](01-compose-iteration-operations.md) through
[6](06-iteration-counts-and-state.md). This also touches general resource
control flow, beyond collection ownership summaries.

## Goal

Reuse the checked loop model for unconditional loops and explicitly account for
ownership and peak usage on every exit edge. Iterator lowering and `for` support
are covered by [task 8](08-for-loops-and-iterators.md).

## Supported boundary

Lexical edges carry live values, allocations, detached results, and peak history.
Scope cleanup and memory-section composition apply to normal completion and
explicit exits, including nested and labelled exits. Loops without a local back
edge reuse Verus's nonisolated/no-back-edge proof form, including value breaks.

Reusable ownership summaries admit effect-free loop-head inequality breaks that
refine the same counter comparison, or supply it for an unconditional loop.
Current-loop continuations compose under supported scalar flags and counter
thresholds when the complete visit has checked progress. Head exits retain the
completed input regions and preceding iterations' peaks. Exit-count ensures are
proved at every exit; partial visits cannot export completed-visit facts.

Reusable value breaks, unrepresentable stopping counts, partial exits that change
fixed ownership roles or original regions, and operand-level exits remain
unsupported. Returned owning alternatives require compatible proof-state
identities and frozen descriptors. These restrictions reject explicitly rather
than substituting aggregate ownership. Supported iterators are covered by task 8.

## Work

- [x] Represent normal completion, continuation, break, and function return with
  their live ownership and allocation lifetimes.
- [x] Preserve scope cleanup and peak history on every edge, including nested and
  labelled exits and interaction with budgeted memory sections.
- [x] Admit unconditional loops and value-producing breaks where the exit
  transformation is representable.
- [x] Check frontend, macro, and verification boundaries according to the
  project instructions; do not build a parallel loop accounting implementation.

## Completion criteria

Tests cover early termination, skipped iterations, nested exits, returned owning
values, and cleanup of temporary allocations. Equivalent supported while and
unconditional-loop traversals preserve caller-visible ownership and peak bounds.
Unsupported exit dependencies have explicit rejection tests. Document the
resulting source subset, including inherited Verus loop restrictions. Supported
`for` iterators are covered separately by task 8.

## Starting points

- [Loop admission](../../../../../source/vir/src/resource/memory/loops.rs)
- [Body proof driver](../../../../../source/vir/src/resource/memory/loops/analysis.rs)
- [Expression accounting](../../../../../source/vir/src/resource/memory/analysis.rs)
- [Lexical exit states](../../../../../source/vir/src/resource/memory/control.rs)
- [Exit regressions](../../../../../source/rust_verify_test/tests/resource/memory/control_flow.rs)
- [Storage and exit tests](../../../../../source/rust_verify_test/tests/resource/memory/storage.rs)
- [Loop checkpoint tests](../../../../../source/rust_verify_test/tests/resource/memory/checkpoints.rs)
