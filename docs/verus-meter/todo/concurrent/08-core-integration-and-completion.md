# 08. Core integration and completion

Dependencies: 01–07. All code paths below are relative to the repository root.

## Goal

Close the complete approved capability set. This is an integration and soundness
review of already implemented areas, not a place to defer missing core behavior
or the first time tests are written.

## Work

- [ ] Review every [core capability](README.md#core-capability-coverage) against
  implementation and named executable tests. Reconcile the operation matrix from 01 with actual supported
  APIs, outcomes and restrictions. Resolve gaps in their owning task; reopen and
  move that TODO out of `complete/` if its completion criteria no longer hold.
- [ ] Audit trusted contracts and generated obligations together: compiler identity,
  synchronization instance, acquisition lifetime, allocation identity, ownership
  transfer, primitive workspace, shared roots, pending results and release order.
  Ensure ordinary functional external specs never silently imply memory effects.
- [ ] Review actual execution paths for missing events, including implicit drops,
  early exits, blocked workers, helper release, failed acquisition and the selected
  error/panic boundary. Verify excluded operations produce explicit failures.
- [ ] Complete end-to-end examples for standard mutexes, bounded permits and a
  custom Verus-verified protocol. Include symbolic workers/sizes, helper factoring,
  shared allocations and results that outlive synchronization or worker completion.
- [ ] Ensure acceptance tests mutate executable allocation and synchronization code
  without manually changing accounting ghosts. Verify that invalid tight bounds
  fail and legal retained storage succeeds with sufficient allowance.
- [ ] Pair two end-to-end cases using the same mutex. In one, four workers each
  create and drop scratch before unlocking. Allow one worker's scratch in the
  total bound. In the other, each worker pushes an owning element into a shared
  vector created with zero reservation. Verify a total bound derived from the
  modeled slots, payloads and other live storage, with no private resize
  allowance. After all joins, check current storage with all four slots and
  payloads still live. A bound allowing only one retained element must fail there.
- [ ] Document the supported source-memory guarantee, contract/proof usage,
  primitive trust boundary, scope restrictions and useful diagnostics. Clearly
  distinguish source bytes from physical RAM, allocator overhead and OS stacks.
  Update existing model/example guidance instead of creating a status-log archive.
- [ ] Run applicable full validation against the rebuilt verifier. Record precise
  commands/results and material limitations in the implementation commit messages.
- [ ] Record evidence for the core capabilities. Move this document
  to `complete/` only when the whole core checklist is satisfied and no required
  implementation or verification work remains.

## Completion criteria

The implementation covers the core capabilities and supported-operation matrix
end to end. Standard contracts reuse Rust guarantees; custom protocols
use Verus proofs; both automatically constrain actual allocation lifetimes.
Symbolic total bounds compose across calls and thread boundaries without missing
or double-counted storage. Diagnostics and documentation reflect actual support.
No partial demonstration, untested assumption, disabled check or silently dropped
requirement substitutes for completion.

## Validation

Use the README's memory suite, affected frontend/parser/mode/erasure/atomic and
function-contract regressions, formatting and Clippy. Run strict rustdoc for
public API/documentation-lint changes and focused checks for executable examples.
Use the prepared pinned tools and Rust test orchestration. Complete a final staged
diff review, preserve unrelated changes and commit validated work locally.

Do not repeat unchanged successful checks without a new change or unresolved
concern; broaden checks where the integration review exposes another affected
boundary. Do not mark this task complete while material checks remain unrun or
failing. Explain and leave it open if an external blocker prevents validation.

## Decisions from TODO 01

Audit the concrete surface, cost table, certificate obligations and all transition
review cases in `docs/verus-meter/concurrent-model.md`. Check both implementation
and fail-closed diagnostics for every row of the scope matrix, including nested
workers, strong Arc final drops, protected owners, implicit guard release and the
panic-free domain. Compare new static/runtime model sizes and verify that the
model-version change does not silently alter existing sequential contracts.

## Starting points

- `docs/verus-meter/concurrent-model.md`
- `docs/model.md`
- `examples/resource/memory/README.md`
- `source/rust_verify_test/tests/resource.rs`
- `source/rust_verify_test/tests/resource/memory/mod.rs`
- `source/rust_verify_test/tests/examples.rs`
