# 6. General iteration counts and carried state

Builds on the ownership transformations in tasks
[1](01-compose-iteration-operations.md) through
[5](05-borrowed-and-incoming-ownership.md).

## Goal

Determine precise ownership repetition and supported scalar exit state through
a shared checked progress model.

## Supported boundary

Both ownership planners consume a shared comparison-gap model. Integer locals
can make literal constant additions or subtractions. Comparisons may be strict or
inclusive in either direction. Either side can change when their relative gap
closes by a positive constant. Checked collection-length transitions also supply
progress, including several removals per visit and a partial final block.
Zero visits preserve the original state. Additional integer locals with supported
translations retain their exact exit values, including for later allocations.

The body proof counts actual back edges in erased state. Scalar relationships,
monotone collection lengths, preserved length frames, and branch-selected prefix
lengths become ordinary invariants, proved at entry and on every back edge.
Shared immutable entry observations keep progress, charge conservation, and
allocation headroom related in isolated and nested loop queries. Functions with
ownership interfaces or template calls preserve runtime-child classification
across producing loops, including directly built inputs to later helpers.

Allocation envelopes use symbolic invariant bounds and interval arithmetic over
visit ordinals. Completed nested visits carry their growth candidates into the
containing proof, including counts depending on current outer scalar state.
Operation-site bounds and integer overflow checks remain mandatory. Pointwise
proved multiplication facts connect symbolic per-visit amounts to total headroom.

Stationary-path overwrites and affine descriptor updates can provide complete
closed forests beyond the finite normalization window. Their base and successor
forest equalities are checked and a generic induction proves the result. This
retains individual allocations, logical geometry, and caller extraction views.
Empty retained ranges expose an empty forest without unfolding each child.
Other programs retain their exact recurrence; they do not receive an aggregate
ownership replacement or automatic closed-form proof.

Payload-dependent progress, geometric updates, conditional scalar translations,
comparisons of two shrinking lengths that saturate at zero, and arithmetic
wrappers around shrinking-length progress need a richer checked relation. They
reject when a precise ownership summary is required, as do other unsupported
scalar dependencies. This task does not provide arbitrary recurrence inference.
Termination checking remains separate. Loop exits and unconditional forms are
covered by [task 7](07-loop-forms-and-exits.md); `for` and iterator support
remains in [task 8](../08-for-loops-and-iterators.md).

## Work

- [x] Define a checked progress/count interface consumed by ownership repetition,
  independently of the source spelling of the loop condition.
- [x] Support representable countdowns and non-unit strides, including zero
  iterations and ranges whose length is not a multiple of the stride.
- [x] Carry supported scalar recurrences and their exit values without allowing
  temporary iteration symbols to escape.
- [x] Generate collection-length invariants from checked iteration effects and
  progress, such as `length = initial_length + 2 * completed_iterations` for two
  appends per iteration. Prove generated relationships at loop entry and on back
  edges; do not assume them from the ownership summary.
- [x] Classify changing bounds and data-dependent stopping conditions. Implement
  those with a precise representable relation; explicitly reject the rest.
- [x] Broaden checked allocation-envelope inference beyond literal ceilings in
  invariants, including symbolic bounds and observations inherited from enclosing
  loops. Keep operation-site extent checks and complete allocation descriptors.
- [x] Extend cost and indexed-view induction for evolving forest recurrences
  beyond their finite normalization window. Preserve the exact recurrence for
  larger counts and avoid expanding unrelated descriptor views in failing-budget
  queries.
- [x] Preserve integer overflow obligations and distinguish loop termination
  proofs from the ownership facts needed to describe completed iterations.

## Completion criteria

Equivalent supported traversals with different counter forms produce consistent
ownership summaries. Tests cover boundary counts, final scalar values, overflow,
and nested loops whose counts use supported outer state. Document the accepted
recurrence and stopping-condition classes; do not claim arbitrary recurrence
inference.

The [batched-construction example](../../../../../examples/resource/memory/heap/loops/batched_construction.rs)
must verify without its handwritten `buffers.len() == 2 * batch` invariant.

## Starting points

- [Shared control classification](../../../../../source/vir/src/resource/memory/loops.rs)
- [Shared counts and scalar transitions](../../../../../source/vir/src/resource/memory/loops/progress.rs)
- [Checked progress evaluation](../../../../../source/vir/src/resource/memory/transfer/trace/loops/progress.rs)
- [Complete closed-forest candidates](../../../../../source/vir/src/resource/memory/transfer/iteration.rs)
- [Progress and ownership regressions](../../../../../source/rust_verify_test/tests/resource/memory/progress_loops.rs)
