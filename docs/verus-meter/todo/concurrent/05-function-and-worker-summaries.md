# 05. Function and worker summaries

Dependencies: 01–04. All code paths below are relative to the repository root.

## Goal

Preserve synchronization identities, lifetimes and ownership effects across calls
and spawned workers so tight bounds compose without whole-program inlining.

## Work

- [ ] Extend checked function summaries with synchronization-instance parameters,
  acquisition/release effects, conditional simultaneous footprints, and retained
  input/result ownership. Reuse existing transfer templates and lifetime profiles.
- [ ] Instantiate scalar inputs, shared/owned allocation identities and guard/permit
  relationships at calls and spawn sites. Preserve equal aliases and distinct
  actual instances; fresh acquisitions must not alias an earlier acquisition.
- [ ] Support helpers that allocate under an incoming guard, acquire internally,
  release a guard, consume a buffer, or return supported owned storage/guards.
  Export the pre-acquisition, acquired and post-release storage needed by callers.
- [ ] Keep caller-live storage during helper work. Preserve early scratch versus
  late-result precision and declared contract slack; do not subtract independent
  peaks or infer hidden phase guarantees from a scalar allowance.
- [ ] Compose through supported conditional paths and loops, retaining ordering and
  effects. Validate representability before publishing a summary. Missing ownership
  or synchronization interfaces are errors even with a generous numeric bound.
- [ ] Handle worker summaries through the same footprint/effect interfaces while
  keeping asynchronous lifetime semantics distinct from ordinary calls.
- [ ] Preserve the existing call-graph soundness policy. Admit new closure/generic
  or imported forms only as specified in 01, with checked or explicitly trusted
  interfaces and appropriate model compatibility; do not broadly relax eligibility.

## Completion criteria

Equivalent supported operations written directly or inside helpers preserve the
same ownership/synchronization relationships needed for tight composition.
Returned allocations retain identity and cost, releases in helpers end the correct
acquisition, and equal/different lock arguments remain equal/different. Summaries
are derived and checked against bodies or come from explicit trusted contracts.

## Validation

Pair direct and factored versions of allocation, drop, transfer and release.
Test two aliases passed to a helper, distinct locks of one type, nested helpers,
helper-returned buffers, caller-retained inputs, guard effects and worker results.
Negative tests include wrong-instance substitution, hidden extra allocation,
missing summary and unjustified post-release lifetime assumptions. Run the README
memory checks and upstream function-contract/closure regressions as applicable.

## Starting points

- `source/vir/src/resource/memory/summary.rs`
- `source/vir/src/resource/memory/calls.rs`
- `source/vir/src/resource/memory/contracts.rs`
- `source/vir/src/resource/memory/transfer/mod.rs`
- `source/vir/src/resource/memory/ownership.rs`
- `source/rust_verify_test/tests/resource/memory/storage_calls.rs`
- `source/rust_verify_test/tests/resource/memory/return_sharing.rs`
