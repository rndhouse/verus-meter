# 2. Conditional ownership effects

Depends on [task 1](01-compose-iteration-operations.md).

## Goal

Compose branch-dependent ownership changes across iterations while preserving
the relationship between the branch decision and the resulting allocations.

## Supported boundary

Guarded `if` effects use the same checked block composition as unconditional effects.
A counted loop can select fresh appends, last-element removals, whole-child
restoration, or routing unchanged children to alternative fixed destinations.
Original-input lifetimes join with the same conditions as complete forests;
intermediate branch allocations retain their peak checks.

Iteration-invariant decisions may use constants and immutable scalar parameters.
Varying decisions compare the counter itself with thresholds built from those
inputs and constants, using
`<`, `<=`, `>`, `>=`, `==`, or `!=`, in either operand order. Boolean combinations
and counter windows use the same interval partition. Clipped, sorted thresholds
provide exact nonnegative widths in iteration order, including empty, singleton,
and out-of-range selections. Each interval selects a complete program rather
than assuming every guarded operation executes.

Payload tests, changing collection observations, arithmetic on the counter in
predicates, and new control/count forms remain unsupported. Every represented
branch program must satisfy task 1's disjoint-role, monotone-block, and whole-child
flow rules. Conditions on separate decisions are not solved to rescue an
incompatible program. Runtime-indexed roles, mixed growth/removal on one role
within a selected program, partial routing within an extraction block, and
transformed children remain
outside this boundary. An enclosing loop can repeat a completed guarded program
only when it also satisfies these composition rules.

Persistent fixed ownership slots must survive both branches. Iteration-local
children may move to alternative destinations when both branches consume them;
branch-dependent surviving local owners remain unsupported. Consuming loops
require a unit removal on every represented path. Symbolic expansion rejects
more than six distinct decisions or sixteen distinct threshold boundaries.

## Work

- [x] Represent guarded iteration effects and ownership joins using the shared
  composition mechanism.
- [x] Distinguish an iteration-invariant condition from a condition that varies
  with the iteration or payload. Define which predicates can be summarized and
  how their selection counts and child ordering are represented.
- [x] Handle conditional insertion/removal and routing a whole child to one of
  multiple destinations without assuming that every branch executes.
- [x] Preserve allocation lifetimes and peak checks on each path, including
  branches that leave ownership unchanged.

## Completion criteria

Tests exercise no selected iterations, all selected iterations, mixed selections,
and alternative destinations. Caller extraction observes the correct surviving
children and order. Excess usage fails verification; unrepresentable predicates
reject rather than producing a guessed aggregate footprint. Document any
remaining predicate restrictions explicitly.

## Starting points

- [Iteration analysis](../../../../../source/vir/src/resource/memory/transfer/trace/loops.rs)
- [Ownership evaluator](../../../../../source/vir/src/resource/memory/transfer/trace.rs)
- [Guarded interval programs](../../../../../source/vir/src/resource/memory/transfer/trace/loops/guards.rs)
- [Conditional loop regressions](../../../../../source/rust_verify_test/tests/resource/memory/conditional_loops.rs)
- [Helper control-flow regressions](../../../../../source/rust_verify_test/tests/resource/memory/helper_control.rs)
- [Loop dependency regressions](../../../../../source/rust_verify_test/tests/resource/memory/loop_ownership.rs)
