# 07. Symbolic concurrent bound composition

Dependencies: 01–06. All code paths below are relative to the repository root.

## Goal

Prove total symbolic peak bounds using the allocation, worker, synchronization
and summary information already implemented. Tight synchronization-aware bounds
must work through the normal compiler analysis for standard and custom protocols.

## Work

- [ ] Compose simultaneous footprints under verified synchronization constraints,
  preserving symbolic worker counts, allocation sizes and permit capacity.
  Keep shared allocations, caller storage and retained results disjointly charged.
- [ ] Derive phase/count relationships from actual spawn/join and protocol events.
  Generate inductive proof obligations rather than enumerate concrete schedules
  or assume a user-supplied population counter matches execution.
- [ ] Support unconstrained `n * b`, exclusive `b` for nonzero `n`, and
  `min(n, k) * b` under the required per-holder/capacity/lifetime conditions.
  Zero workers contribute zero scratch. Include all other storage in total bounds.
- [ ] Preserve conditions through branches, calls, worker overlap and sequential
  reuse. Check intermediate allocation/reallocation peaks and blocked storage,
  not merely synchronization endpoints. Whole-call peaks cannot replace phase
  information when a tight proof depends on it.
- [ ] Integrate assertions with the existing symbolic proof generation and range
  policy. Keep memory metadata erased and generated checks verified. Solver failure
  or timeout must not become an assumed bound.
- [ ] Support additional invariants and arithmetic lemmas when inference is
  insufficient. Preserve the expression forms selected in 01; report unsupported
  forms or precision limits rather than silently changing the claimed guarantee.
- [ ] Implement supported concurrent section/checkpoint/query semantics from 01,
  or their explicit restrictions. Do not accidentally interpret a whole-operation
  bound as a thread-local current/peak query or change runtime-query guarantees.
- [ ] Finish source diagnostics distinguishing exceeded bounds, missing lifetime or
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

## Starting points

- `source/vir/src/resource/memory/footprint.rs`
- `source/vir/src/resource/memory/accounting.rs`
- `source/vir/src/resource/memory/contracts.rs`
- `source/vir/src/resource/memory/symbolic.rs`
- `source/vir/src/resource/memory/growth.rs`
- `source/rust_verify_test/tests/resource/memory/reachability.rs`
- `source/rust_verify_test/tests/resource/memory/call_budgets.rs`
