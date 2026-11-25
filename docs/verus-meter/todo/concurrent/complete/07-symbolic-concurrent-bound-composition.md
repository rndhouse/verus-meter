# 07. Symbolic concurrent bound composition

Dependencies: 01–06. All code paths below are relative to the repository root.

## Goal

Prove total symbolic peak bounds using the allocation, worker, synchronization
and summary information already implemented. Tight synchronization-aware bounds
must work through the normal compiler analysis for standard and custom protocols.

## Implementation order

Work through these five documents in order. Each child delivers checked behavior
through the ordinary verifier and pairs an accepted total bound with a failure
that depends on executable code. Follow the validation and completion procedure
in the concurrent TODO index for each child. Close 07 after the five children
and the original checklist below have evidence.

- [x] [07.1 — Fixed workers and mutual exclusion](07.1-fixed-worker-peak.md). Prove a total bound for two workers using one mutex.
- [x] [07.2 — Symbolic worker counts](07.2-symbolic-worker-counts.md). Extend the same proof from two workers to a symbolic number of workers.
- [x] [07.3 — Permits and verified protocols](07.3-permits-and-verified-protocols.md). Use verified capacity and reader/writer guarantees in total bounds.
- [x] [07.4 — Helpers, retained storage and nested workers](07.4-helpers-and-retained-storage.md). Preserve tight totals through calls, transfers, repeated acquisition and nested spawns.
- [x] [07.5 — Sections, checkpoints and diagnostics](07.5-sections-queries-and-diagnostics.md). Apply the global proof to scoped observations and explain unproved bounds.

## Work

- [x] Compose simultaneous footprints under verified synchronization constraints,
  preserving symbolic worker counts, allocation sizes and permit capacity.
  Keep shared allocations, caller storage and retained results disjointly charged.
- [x] Derive phase/count relationships from actual spawn/join and protocol events.
  Generate inductive proof obligations rather than enumerate concrete schedules
  or assume a user-supplied population counter matches execution.
- [x] Support unconstrained `n * b`, exclusive `b` for nonzero `n`, and
  `min(n, k) * b` under the required per-holder/capacity/lifetime conditions.
  Zero workers contribute zero scratch. Include all other storage in total bounds.
- [x] Preserve conditions through branches, calls, worker overlap and sequential
  reuse. Check storage held while blocked and every modeled intermediate peak,
  including two explicitly created buffers whose lifetimes overlap. For a
  guarded push, compose the vector's documented slot and payload charges.
  Its private resize contributes no additional peak. Preserve phase information
  when a tight proof depends on it.
- [x] Integrate assertions with the existing symbolic proof generation and range
  policy. Keep memory metadata erased and generated checks verified. Solver failure
  or timeout must not become an assumed bound.
- [x] Support additional invariants and arithmetic lemmas when inference is
  insufficient. Preserve the expression forms selected in 01; report unsupported
  forms or precision limits rather than silently changing the claimed guarantee.
- [x] Implement supported concurrent section/checkpoint/query semantics from 01,
  or their explicit restrictions. Do not accidentally interpret a whole-operation
  bound as a thread-local current/peak query or change runtime-query guarantees.
- [x] Finish source diagnostics distinguishing exceeded bounds, missing lifetime or
  synchronization evidence, and unsupported operations. Identify contributing
  allocations, instances, retained results and release boundaries where available.

## Completion criteria

Real supported concurrent programs verify parameterized total byte bounds through
both trusted standard synchronization and Verus-verified custom protocols.
The tighter scratch contribution is established by compiler-derived allocation
lifetimes and verified synchronization, while all non-scratch storage has checked
costs. Factoring code into supported helpers preserves the necessary precision.

## Validation

Check symbolic `n`, `b` and `k`, zero/one/many workers, several live allocations
under one guard, shared roots, retained results, helper calls, repeated acquisition
and loop reuse. Include negative mutations for pre-lock allocation, early unlock,
different locks, false permit bounds, insufficient bytes and hidden helper costs.
A legal escaping allocation must verify with an adequate retained-storage bound.

Use exact necessary live contributions for too-small-bound tests: subtracting one
from an already loose total envelope need not fail. If tests inspect a scratch
projection, define it from compiler-owned allocation identities and also verify
total storage; it must not exempt other allocations from accounting. Run all
applicable README checks after building the changed verifier.

## Decisions from TODO 01

Implement the global proof and query rules in
`docs/verus-meter/concurrent-model.md`:

- [x] Generate initialization/preservation obligations for coverage, protocol state,
  worker-family counts and the simultaneous byte envelope under interference.
  Local effect graphs cannot assume other threads stop during helper execution.
- [x] Compose acyclic worker trees and finite phase families with symbolic
  multiplicities. Retain source budget grammar and u64 obligations; use ordinary
  verified lemmas for aggregate envelopes requiring additional reasoning.
- [x] Bound sections/checkpoints over their full covered subtree, require joins
  before section exit, and preserve fixed checkpoint/section bound restrictions.
  Reject cross-thread ancestor checkpoint references. Runtime peak queries still
  evaluate declared formulas, and all admitted new size queries must agree with
  the static model.

## Starting points

- `source/vir/src/resource/memory/footprint.rs`
- `source/vir/src/resource/memory/accounting.rs`
- `source/vir/src/resource/memory/contracts.rs`
- `source/vir/src/resource/memory/symbolic.rs`
- `source/vir/src/resource/memory/growth.rs`
- `source/rust_verify_test/tests/resource/memory/reachability.rs`
- `source/rust_verify_test/tests/resource/memory/call_budgets.rs`

## Completion review

The five child documents record the executable cases for each part of the proof.
Together they cover the original criteria on the supported worker domains.

- Fixed workers use outstanding completion tags and guard identities. Two workers
  on one mutex verify `b + 108` and reject one byte less. Pre-lock allocation,
  early unlock and different mutexes each invalidate the single-buffer bound.
  [Fixed-worker evidence](07.1-fixed-worker-peak.md)
- Counted workers use erased counts from actual publications and joins. Source
  loop invariants and ordinary Verus arithmetic facts discharge the generated
  obligations. Tests cover zero workers, reuse after draining, false population
  limits and overflowing source budgets. Verified capacities bound compatible
  holders by the smaller of `n` and `k`.
  [Counted workers](07.2-symbolic-worker-counts.md) · [Verified protocols](07.3-permits-and-verified-protocols.md)
- Checked helpers and nested fixed workers preserve guard identity, overlapping
  buffers and retained results. Distinct allocations and occupied vector slots
  remain charged through release and delivery. Shared payloads require a history
  that covers all updates. A transient worker cost without a provable summary
  still fails its original byte obligation.
  [Helpers and retained storage](07.4-helpers-and-retained-storage.md)
- Current and peak assertions use their nearest budgeted scope, including covered
  descendants. The declared runtime query was compiled and exercised. Unsupported
  history, insufficient bytes and unproved symbolic bounds have separate tests.
  [Scoped proofs and integrated validation](07.5-sections-queries-and-diagnostics.md)

The [completed core integration audit](08-core-integration-and-completion.md)
records end-to-end validation across the numbered tasks.
