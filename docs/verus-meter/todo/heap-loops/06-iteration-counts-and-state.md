# 6. General iteration counts and carried state

Builds on the ownership transformations in tasks
[1](complete/01-compose-iteration-operations.md) through
[5](complete/05-borrowed-and-incoming-ownership.md).

## Goal

Separate ownership effects from the current two recognized progress patterns,
so supported scalar transitions can determine iteration counts and exit state.

## Current restriction

Ownership summaries recognize a counter below a stable upper bound with a unit
increment, or a collection length above a stable lower bound with one removal. Other
strides, countdowns, changing bounds, and updates to additional persistent scalar
state are not generally supported. Reads and dependencies involving collections
modified by the iteration also restrict summary construction.

Local memory proofs still require handwritten collection-length invariants to
connect counter progress with checked collection operations, even when the
ownership summary already represents those operations.

## Work

- [ ] Define a checked progress/count interface consumed by ownership repetition,
  independently of the source spelling of the loop condition.
- [ ] Support representable countdowns and non-unit strides, including zero
  iterations and ranges whose length is not a multiple of the stride.
- [ ] Carry supported scalar recurrences and their exit values without allowing
  temporary iteration symbols to escape.
- [ ] Generate collection-length invariants from checked iteration effects and
  progress, such as `length = initial_length + 2 * completed_iterations` for two
  appends per iteration. Prove generated relationships at loop entry and on back
  edges; do not assume them from the ownership summary.
- [ ] Classify changing bounds and data-dependent stopping conditions. Implement
  those with a precise representable relation; explicitly reject the rest.
- [ ] Broaden checked allocation-envelope inference beyond literal ceilings in
  invariants, including symbolic bounds and observations inherited from enclosing
  loops. Keep operation-site extent checks and complete allocation descriptors.
- [ ] Extend cost and indexed-view induction for evolving forest recurrences
  beyond their finite normalization window. Preserve the exact recurrence for
  larger counts and avoid expanding unrelated descriptor views in failing-budget
  queries.
- [ ] Preserve integer overflow obligations and distinguish loop termination
  proofs from the ownership facts needed to describe completed iterations.

## Completion criteria

Equivalent supported traversals with different counter forms produce consistent
ownership summaries. Tests cover boundary counts, final scalar values, overflow,
and nested loops whose counts use supported outer state. Document the accepted
recurrence and stopping-condition classes; do not claim arbitrary recurrence
inference.

The [batched-construction example](../../../../examples/resource/memory/heap/loops/batched_construction.rs)
must verify without its handwritten `buffers.len() == 2 * batch` invariant.

## Starting points

- [Shared control classification](../../../../source/vir/src/resource/memory/loops.rs)
- [Count and scalar-state checks](../../../../source/vir/src/resource/memory/transfer/trace/loops.rs)
- [Ownership scalar evaluation](../../../../source/vir/src/resource/memory/transfer/trace.rs)
- [Loop ownership tests](../../../../source/rust_verify_test/tests/resource/memory/loop_ownership.rs)
