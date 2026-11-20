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

## Remaining shared payload work

Two workers can hold strong handles to the same mutex while acquiring it in either order.
Today a worker knows the mutex identity and its strong-handle count. It has no description
of the contents another holder could leave behind. A two-worker program that pushes and
pops from the same vector is therefore rejected at the first protected write even with a
4,096-byte allowance.

- [ ] At each acquiring outcome, bind the current contents to the canonical root and guard
  interval, including worker and loop occurrence. Carry allocation origins, logical
  length, reservation and owned elements. Guard moves and helper calls reuse that binding.
  A poisoned result owns the acquisition. `WouldBlock` opens none.
- [ ] Use checked operations and ownership templates to describe the contents before and
  after a write. Keep old and new allocations charged while they coexist. When a pop moves
  an allocation into a result, connect its caller-side ownership path to the generating
  exit and forest projection. It can survive unlock and the final drop of the mutex.
- [ ] Publish the updated contents at release. A subsequent acquisition of the same root
  reads the state left by the previous holder. Different roots remain independent. Worker
  checkpoints currently get imported backing costs at publication in
  `source/vir/src/resource/memory/shared/phases.rs`. Mutable backing needs its cost at
  the checkpoint. Join transfers results and strong handles. Replaying writes in join
  order would lose legal updates.
- [ ] Test two outstanding writers with distinguishable legal outcomes, reversed joins,
  direct and factored operations, a retained popped box, and a one-byte-short local bound.
  Until the effects are available, reject use of stale contents.

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
