# 01. Concurrent semantics and supported scope

Dependencies: none. Read the approved plan and the workflow in the concurrent
README before starting. All code paths below are relative to the repository root.

## Goal

Define the complete core's accounting and proof interfaces before implementation.
Design synchronization semantics, automatic lifetime relationships and function
summaries together. This task completes the specification, not the feature.

## Work

- [ ] Specify the accounting scope of a concurrent contract, including coordinator,
  descendants, blocked workers, captured values, shared allocations and results
  retained after worker completion. Define entry storage and ownership at exit.
- [ ] Define source-level events and their ordering: allocation, replacement,
  transfer, acquisition, release, spawn publication, completion and join. Include
  transient overlap and every supported early exit. Preserve the existing model's
  distinction between inline storage and separate allocations.
- [ ] Define the proof connection: every live modeled object remains covered;
  synchronization contracts constrain states; lifetime relationships connect
  actual storage to those states; simultaneous footprints imply the byte bound.
  Explain initialization, preservation and interference between worker steps.
- [ ] Specify instance identity separately from acquisition identity. Design the
  summary interface for both trusted primitives and custom verified protocols,
  including symbolic input substitution, retained results and guard effects.
- [ ] Define a developer-facing proof interface that keeps symbolic byte contracts
  and permits additional invariants/lemmas without manual allocation counters or
  byte credits. Separate supplied primitive guarantees from generated obligations.
- [ ] Record a concrete supported-operation matrix: thread APIs and captures,
  shared-ownership operations, standard mutex operations, a concrete semaphore
  implementation/interface, atomic primitives/orderings, and custom protocol proof
  forms. Include library workspace/layout policy and trusted dependencies.
- [ ] Resolve the approved plan's open scope questions explicitly: nested spawning,
  detach, panic/unwinding, custom destructors, channels, async cancellation and
  delayed reclamation. Justify exclusions and specify rejection behavior. Do not
  exclude standard mutexes, bounded permits, custom protocols, symbolic counts,
  helpers or retained allocations to make the task easier.
- [ ] Put lasting semantics in the model documentation and beside the relevant
  interfaces. Carry any additional required implementation into the downstream
  tasks before marking this task complete; do not leave an unassigned requirement.

## Completion criteria

A developer can determine, without inventing rules, which storage counts at each
transition and which facts are trusted, verified or compiler-derived. The design
covers both `n * b` and synchronization-constrained scratch bounds through the
same representation. No intermediate representation discards synchronization
relationships in favor of independent scalar worker peaks.

The operation matrix assigns every supported behavior to a later task and every
excluded behavior to an explicit diagnostic requirement. Material changes to the
approved feature require user agreement; routine interface choices do not.

## Validation

Walk the semantics through allocation before lock, early unlock, two aliases of
one lock, distinct locks, release/reacquisition, several buffers under one guard,
shared views of that guard, a returned buffer and a completed unjoined worker.
Check that every live charge has a defined owner/accounting location throughout.
Check documentation links and `git diff --check`; no rebuild is required for a
specification-only change. Follow the README validation rules if code changes.

## Starting points

- `docs/verus-meter/model.md`
- `source/rust_verify/src/resource/memory/pipeline.rs`
- `source/vir/src/resource/memory/model.rs`
- `source/vir/src/resource/memory/summary.rs`
- `source/vir/src/resource/memory/accounting.rs`
- `source/vstd/thread.rs`
- `source/vstd/invariant.rs`
