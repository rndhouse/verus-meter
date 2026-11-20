# 05. Function and worker summaries

Dependencies: 01–04, including the checked worker-summary foundation in 03.2 and
population substitutions in 03.3. All code paths below are relative to the
repository root.

## Goal

Preserve synchronization identities, lifetimes and ownership effects across calls
and spawned workers so tight bounds compose without whole-program inlining.

## Integration boundary

03.2 owns the summary machinery necessary to connect executable worker bodies to
entry, completion and native/vstd join, including the required Result handling.
03.3 connects occurrence substitutions, nested workers and global shared ownership.
Those tasks must not wait for 05. This task extends their common checked interface
with 04's allocation/synchronization relationships for general helper composition,
guard returns and protected owning payloads. Avoid a parallel worker summary format
or a second implementation of lifecycle accounting.

## Work

- [x] Extend the checked summary foundation from 03.2 with instance parameters,
  acquisition/release effects, conditional simultaneous footprints, and retained
  input/result ownership. Reuse existing transfer templates and lifetime profiles.
- [ ] Instantiate scalar inputs, shared/owned allocation identities and guard/permit
  relationships at calls and spawn sites. Preserve equal aliases and distinct
  actual instances; fresh acquisitions must not alias an earlier acquisition.
- [x] Support helpers that allocate under an incoming guard, acquire internally,
  release a guard, consume a buffer, or return supported owned storage/guards.
  Export the pre-acquisition, acquired and post-release storage needed by callers.
- [x] Keep caller-live storage during helper work. Preserve early scratch versus
  late-result precision and declared contract slack; do not subtract independent
  peaks or infer hidden phase guarantees from a scalar allowance.
- [ ] Compose through supported conditional paths and loops, retaining ordering and
  effects. Validate representability before publishing a summary. Missing ownership
  or synchronization interfaces are errors even with a generous numeric bound.
- [ ] Apply the added lifetime/footprint composition to existing checked worker
  summaries through the same interfaces. Preserve asynchronous execution and
  caller-live storage; verify that factored worker code retains direct-code
  precision rather than rebuilding body entry/completion here.
- [x] Preserve the existing call-graph soundness policy. Admit new closure/generic
  or imported forms only as specified in 01, with checked or explicitly trusted
  interfaces and appropriate model compatibility; do not broadly relax eligibility.

## Implemented in `701ce914f`

Checked helpers now preserve the actual native mutex, incoming and returned guards, and
storage live at each wait and release. The same call machinery runs inside workers. A
fixed worker can also take ownership of a protected allocation tree when it receives every
strong handle and its result carries no references.

Two source regressions show what survives a call. The caller's release trace reports 37
bytes when a helper drops its scratch before unlocking and 77 bytes when it unlocks first.
After a helper pushes a box through a guard, the caller can pop it and drop both guard and
mutex. The remaining `Option<Box<[u8; 32]>>` passes its 41-byte current-storage check and
fails at 40. Both tests still require the global proof in 07.

Validation passed all 1,192 resource memory tests (including 49 synchronization tests), 88
VIR memory unit tests, 47 resource examples and 133 upstream function and closure tests.
One VIR test and one upstream test are marked ignored. Formatting and the affected Clippy
checks passed.

## Shared mutex payloads in `b8e289e04`

A fixed worker can now use its captured `Arc<Mutex<T>>` even while another actor owns
an alias. At the first owning access through a live guard, the verifier binds the
payload type, allocation root and acquisition to the worker’s source operation. A
guard borrow in a helper uses that same state. At release, the worker records its
outgoing allocation tree, logical vector length, reservation and allocation origins.
A worker can move the guard through nested helpers to a helper that drops it. This
preserves the payload when the calls leave it untouched. The native lock result still
determines which paths own a guard. At first access and release, Verus checks that the
allocation tree describes exactly the bytes entering or leaving the worker’s account.

The executable regressions in
`source/rust_verify_test/tests/resource/memory/synchronization/shared_payloads.rs`
exercise two workers pushing and popping, a guard-taking helper, reversed joins and two
independent mutexes of the same type. For a shared `Box<[u8; 32]>`, the worker’s
current-storage check is exact at 73 bytes outside the guard and 81 inside. Both
one-byte-short checks fail. A worker that replaces a shared vector of unknown length
with an empty vector and pushes one 32-byte box passes a 105-byte check under the guard
and fails at 104.
These are current-storage bounds at the source assertions. The discarded input can still
contribute to an earlier peak.

Validation passed all 1,201 memory integration tests, including 58 synchronization tests,
88 VIR memory unit tests, 47 resource examples and 133 upstream function and closure
tests. One VIR test and one upstream test are marked ignored. Formatting and the
affected Clippy checks passed.

## Remaining shared payload work

- [x] Bind supported owning accesses in fixed workers to the actual captured mutex,
  guard and occurrence. Keep borrow, pop, replacement and release effects tied to
  executable operations. Reject a projected child supplied as the whole cell.
- [x] Count fixed-shape contents once at worker checkpoints. Reject use of an earlier
  vector size at a worker checkpoint, in the owning actor after join, or on unique
  extraction after a peer update. Join order supplies no ordering between writes.
- [ ] Expose the initial protected state and each checked release as alternatives for
  the next acquisition of the same root. Preserve source conditions, occurrence
  identities and allocation origins across proof scopes. Express the outgoing tree in
  terms of the incoming tree and checked inputs so a caller can instantiate the relation
  without referring to another worker’s local proof variables. Include the unchanged state
  on paths that never modify the payload. A vector input is currently arbitrary at
  each acquisition. The two-worker push/pop program still cannot prove its 4,096-byte
  allowance. Test both possible acquisition orders and preserve the transient cost
  while a replacement and the value it displaces coexist. TODO 07 owns the proof
  that all permitted interleavings satisfy the total bound.
- [ ] Connect a popped allocation returned from a worker to the incoming element it
  selected. Check the empty and nonempty outcomes and a one-byte-short bound after it
  escapes the guard. A later observation or extraction of dynamic contents must use
  the state at that point.
- [ ] Carry these transformations through helpers that both change contents and
  consume the guard, multiple access paths under one acquisition, and loop-selected
  shared roots. Indexed backing reservations still require a consistent ownership
  relation for the selected occurrence. Keep unsupported cases explicit.

05 supplies the body-checked transitions. 06 supplies the verified protocol and permit
contracts. 07 proves that the global bound covers the allowed orderings.

## Completion criteria

Equivalent supported operations written directly or inside helpers preserve the
same ownership/synchronization relationships needed for tight composition.
Returned allocations retain identity and cost, releases in helpers end the correct
acquisition, and equal/different lock arguments remain equal/different. Summaries
are derived and checked against bodies or come from explicit trusted contracts.
Worker and helper summaries share the same identity/effect semantics, with the
distinct lifecycle rules already connected in 03. Global interference and total
byte-envelope proofs remain assigned to 07.

## Validation

Pair direct and factored versions of allocation, drop, transfer and release.
Test two aliases passed to a helper, distinct locks of one type, nested helpers,
helper-returned buffers, caller-retained inputs, guard effects and worker results.
Negative tests include wrong-instance substitution, hidden extra allocation,
missing summary and unjustified post-release lifetime assumptions. Run the README
memory checks and upstream function-contract/closure regressions as applicable.

## Decisions from TODO 01

Implement all summary fields specified in `docs/verus-meter/concurrent-model.md`:

- [ ] Complete the scalar/provenance/instance/acquisition/worker binders, alias
  constraints, entry requirements, phase graphs, exit transformations and proof
  dependencies for the full helper surface, extending the foundation from 03.2.
- [ ] Support owning values moved into/out of a mutex-protected shared root,
  primitive-specific lock/try-lock Result matching and proved-success extraction.
  Reuse the Result machinery required for join in 03.2. Changing protected
  ownership updates one persistent descriptor and preserves transients.
- [ ] Summarize standard guard returns and custom witnesses with actual Rust
  borrowing/transfer constraints. Unknown alias relationships cannot establish
  exclusion; scalar contract slack supplies no hidden effect guarantee.

## Starting points

- `source/vir/src/resource/memory/summary.rs`
- `source/vir/src/resource/memory/calls.rs`
- `source/vir/src/resource/memory/contracts.rs`
- `source/vir/src/resource/memory/transfer/mod.rs`
- `source/vir/src/resource/memory/ownership.rs`
- `source/vir/src/resource/memory/workers/body.rs`
- `source/rust_verify_test/tests/resource/memory/storage_calls.rs`
- `source/rust_verify_test/tests/resource/memory/return_sharing.rs`
