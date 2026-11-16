# Concurrent symbolic memory analysis: core implementation plan

## Goal

Extend Verus Meter to verify symbolic peak-memory bounds for concurrent user
code. Use verified properties of the user's synchronization to determine which
allocations can coexist, and derive their costs from executable allocation
lifetimes.

Users retain control over their synchronization implementations. The analysis
must connect to proofs about that code, including custom protocols implemented
with supported atomics. It must not require users to replace their synchronization
with a prescribed collection of Verus Meter locks or semaphores.

This document defines one core feature and its completion checklist. The work
areas below are parts of that feature, not separate prototypes or releases.
Nothing in this plan is marked implemented. Future detailed TODO documents should
map back to this checklist so that outstanding work remains visible.

Background: [high-level explanation](../high-level-concurrent-symbolic-analysis.md),
[technical assessment](../concurrent-symbolic-analysis.md), and the existing
[memory model](../model.md). This plan incorporates the subsequent clarification
that user-defined synchronization is part of the target.

## Required behavior

For `n` workers, each with temporary storage bounded by `b`, the checker should
support both a conservative temporary-storage bound of `n * b` and a tighter
bound derived from synchronization. If a verified protocol guarantees that only
one worker's temporary storage can be alive, that contribution is at most `b`
for nonzero `n`, and zero for `n = 0`.

The total bound must also include shared objects, local storage, handles,
retained results and other modeled allocations. Synchronization reduces only
the contributions whose lifetimes it actually constrains.

Keep symbolic byte expressions as the primary abstraction. Developers supply
invariants and proofs; the compiler derives allocation events, sizes, transfers
and releases. A manually maintained ghost memory counter is not sufficient
evidence for a memory guarantee.

## Work areas

### 1. Define concurrent accounting and the proof connection

Specify what a concurrent resource contract covers: the coordinator, participating
workers, shared storage and results. Define when storage enters and leaves that
accounting scope, including workers that are waiting or have finished but still
have uncollected results.

Design how proved synchronization facts refer to the actual storage whose
lifetimes they constrain. For example, proving exclusive access is useful only
if the analysis also establishes that every relevant live buffer is covered by
that access. The connection must remain valid as other workers execute.

Design this together with function summaries before committing to a representation
that preserves only independent worker peaks. Establish how existing Verus
invariants and tracked proof state support the connection without treating an
entire critical section as one atomic operation.

### 2. Track storage across threads

Extend existing allocation identity and ownership accounting across spawning,
execution, completion and joining. Account for captured values, shared roots,
worker-local storage, and results retained after worker completion.

Moves and ownership transfers must preserve one allocation charge. Shared
references must not multiply the payload charge. Storage must remain counted
until a supported release, even when its original owner or worker has finished.

Support symbolic worker counts and spawning in loops, with proved bounds on
simultaneous outstanding work. Define the supported shared-ownership operations
and worker lifecycle explicitly; unmodeled operations must fail clearly.

### 3. Use synchronization proofs to constrain overlap

Connect verified properties of user code to the memory accounting. Support both
exclusive access and bounds on how many workers can hold relevant storage,
without inferring those properties merely from API names.

Check full allocation lifetimes, including allocation before acquisition,
release before deallocation, repeated acquisition, and transfer to a result or
shared owner. An escaping allocation must remain counted; it cannot disappear
when the synchronization phase ends.

The proof interface must work for user-defined synchronization over supported
primitives. Library integrations should provide reusable specifications and
proofs, not be the only route to tight bounds.

### 4. Preserve precision across functions and workers

Extend function and worker summaries to describe simultaneous storage,
ownership changes, retained results and the synchronization relationships needed
to compose them.

Helpers may allocate, consume, transfer and return supported owning values.
Moving an operation into a helper should preserve the relationships required for
the same tight bound. Include caller storage that remains live during the call,
and distinguish a spawned worker's lifetime from an ordinary function call.

### 5. Prove combined symbolic bounds

Combine the storage that can coexist under the proved synchronization rules.
Handle input-dependent worker counts and allocation sizes, sequential reuse,
shared allocations, and retained data without double counting.

Use inductive proofs and summaries rather than enumerating schedules. Permit
user-supplied invariants and arithmetic lemmas when automatic reasoning is
insufficient. Independent peak summation remains a conservative option within
this design, not its only representation.

### 6. Finish integration and validation

Provide diagnostics that distinguish an excessive bound, an unproved
synchronization relationship, and an unsupported operation. Show the contributing
storage and relevant lifetime boundary where practical.

Complete library integration, regression coverage, executable examples and user
documentation for the agreed supported scope. Preserve existing sequential
memory behavior. Follow the repository's required memory checks and affected
frontend, mode, erasure and function-contract checks when those layers change.

## Core completion checklist

All items are required. A simple mutex example passing does not complete the
feature.

- [ ] Concurrent contracts have explicit accounting, execution and trust semantics.
- [ ] Symbolic worker counts and buffer sizes contribute to checked total bounds.
- [ ] Spawning, captures, waiting workers, completion and joining preserve storage.
- [ ] Supported sharing and ownership transfers neither lose nor duplicate charges.
- [ ] User-defined synchronization proofs constrain actual allocation lifetimes.
- [ ] Both exclusive and bounded-parallel overlap constraints produce tighter bounds.
- [ ] Helpers preserve the synchronization and ownership facts needed for composition.
- [ ] Allocations retained after unlock or worker completion remain accounted for.
- [ ] Adding an executable allocation changes the generated memory obligations
      without requiring a manual ghost-counter update.
- [ ] Negative tests reject too-small bounds, allocation before acquisition,
      early release, unrelated lock instances and extra simultaneous buffers.
- [ ] Tests cover retained results, shared storage and ownership transfers across
      function and thread boundaries, as well as sequential regressions.
- [ ] Unsupported operations fail explicitly; diagnostics and documentation describe
      the completed supported boundary.
- [ ] Required validation passes against the built verifier, with material gaps
      resolved before marking the core complete.

## Scope decisions to settle in the detailed TODOs

Agree on concrete supported operations before implementation: thread APIs,
shared-ownership operations, atomic primitives and ordering guarantees, and
supported ways of expressing synchronization proofs. Supporting user-defined
protocols does not mean that every Rust primitive is already modeled.

Also settle the treatment of nested spawning, detached workers, panic/unwinding,
custom destructors, channels, async cancellation and delayed reclamation. The
previous assessment recommends restricting several of these initially; those
recommendations are not an agreed scope decision. Record each as required for
core completion or explicitly outside the core, with a reason. Do not silently
omit them or call an incomplete requirement finished.

## Execution order and tracking

Design the accounting semantics, synchronization connection and summary interface
together first. Then build the thread accounting and proof integration, complete
composition and symbolic bound checking, and finish the full validation matrix.
Add regression tests alongside each behavior rather than waiting until the end.

Each future TODO should identify the checklist items it delivers, its dependencies
and concrete completion evidence. Keep this checklist as the single overview of
what remains. Implementation commits can be incremental while the definition of
core completion stays fixed; scope changes must be explicit.
