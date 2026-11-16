# 03. Worker lifetimes and shared storage

Dependencies: 01–02. All code paths below are relative to the repository root.

## Goal

Account for all supported worker and shared-storage lifetimes without losing or
multiplying allocation charges. Produce concurrent state for later composition;
spawning must never be handled as a completed ordinary function call.

## Work

- [ ] Implement the thread APIs selected in 01, including closure/capture storage,
  spawn setup/publication overlap, execution, waiting, completion and joining.
  Separate asynchronous spawn edges from ordinary call dependencies.
- [ ] Preserve ownership and synchronization identities through captures, thread
  arguments and returns. Respect executable `Send`/`Sync` requirements; these
  traits alone give no exclusion or memory bound.
- [ ] Implement the selected shared-ownership operations. Count payloads once and
  handles separately. Model supported control-block/reclamation behavior or the
  explicit retained-root restriction from 01. Reject unmodeled weak references,
  leaks or reclamation operations rather than losing their charges.
- [ ] Keep returned allocations charged after completion and before join. Joining
  transfers ownership instead of copying the allocation or freeing it early.
  Waiting workers retain their live local and captured storage.
- [ ] Implement symbolic spawn-loop accounting: distinguish historical spawns,
  outstanding workers and completed results. Generate inductive count/ownership
  obligations and preserve relationships across partial joins and zero iterations.
- [ ] Implement any nested-worker behavior required by 01; otherwise enforce its
  restriction. A parent accounting scope cannot silently close over live children.
- [ ] Handle supported failure paths and explicit exclusions. Dropping a join handle
  must not remove an active worker's storage, regardless of detach policy.

## Completion criteria

Compiler-derived worker states cover every supported lifecycle transition, with
single charges for moved/shared allocations and retained results. A symbolic
worker count describes actual executable spawn/join behavior, not a user-maintained
counter accepted without a connection to those events. No concurrent contract is
accepted without the checks needed to bound its outstanding storage.

## Validation

Test no workers, one worker, symbolic spawn loops, delayed joins, workers returning
owned buffers, shared-root aliases, ownership handoff and blocked-worker storage.
Add negative tests for lost captures/results, duplicate shared payloads, detached
or out-of-scope work, and unmodeled shared-ownership operations. Run the README's
memory checks and affected closure, reference, mode and erasure regressions.

## Starting points

- `source/vstd/thread.rs`
- `source/vstd/std_specs/smart_ptrs.rs`
- `source/vir/src/resource/memory/call_graph.rs`
- `source/vir/src/resource/memory/heap.rs`
- `source/vir/src/resource/memory/lifetime.rs`
- `source/vir/src/resource/memory/loops.rs`
- `source/vir/src/resource/memory/growth.rs`
