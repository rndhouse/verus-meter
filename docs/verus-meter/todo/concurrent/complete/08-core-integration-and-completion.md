# 08. Core integration and completion

Dependencies: 01–07. All code paths below are relative to the repository root.

## Goal

Close the complete approved capability set. This is an integration and soundness
review of already implemented areas, not a place to defer missing core behavior
or the first time tests are written.

## Work

- [x] Review every [core capability](../README.md#core-capability-coverage) against
  implementation and named executable tests. Reconcile the operation matrix from 01 with actual supported
  APIs, outcomes and restrictions. Resolve gaps in their owning task; reopen and
  move that TODO out of `complete/` if its completion criteria no longer hold.
- [x] Audit trusted contracts and generated obligations together: compiler identity,
  synchronization instance, acquisition lifetime, allocation identity, ownership
  transfer, primitive workspace, shared roots, pending results and release order.
  Ensure ordinary functional external specs never silently imply memory effects.
- [x] Review actual execution paths for missing events, including implicit drops,
  early exits, blocked workers, helper release, failed acquisition and the selected
  error/panic boundary. Verify excluded operations produce explicit failures.
- [x] Complete end-to-end examples for standard mutexes, bounded permits and a
  custom Verus-verified protocol. Include symbolic workers/sizes, helper factoring,
  shared allocations and results that outlive synchronization or worker completion.
- [x] Ensure acceptance tests mutate executable allocation and synchronization code
  without manually changing accounting ghosts. Verify that invalid tight bounds
  fail and legal retained storage succeeds with sufficient allowance.
- [x] Pair two end-to-end cases using the same mutex. In one, four workers each
  create and drop scratch before unlocking. Allow one worker's scratch in the
  total bound. In the other, each worker pushes an owning element into a shared
  vector created with zero reservation. Verify a total bound derived from the
  modeled slots, payloads and other live storage, with no private resize
  allowance. After all joins, check current storage with all four slots and
  payloads still live. A bound allowing only one retained element must fail there.
- [x] Document the supported source-memory guarantee, contract/proof usage,
  primitive trust boundary, scope restrictions and useful diagnostics. Clearly
  distinguish source bytes from physical RAM, allocator overhead and OS stacks.
  Update existing model/example guidance instead of creating a status-log archive.
- [x] Run applicable full validation against the rebuilt verifier. Record precise
  commands/results and material limitations in the implementation commit messages.
- [x] Record evidence for the core capabilities. Move this document
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

## Completion evidence

Feature commit `af64bc6e8` on `feature/concurrent-symbolic-analysis` contains the examples and regressions. Source paths below refer to that checkout. Compiler paths beginning with `rust_verify/` are relative to `source/`. The audit covered the operation matrix, transition cases, size table and proof requirements in the concurrent model.

| Capability | Implementation and executable evidence |
| --- | --- |
| Standard primitive identity and trusted costs | `rust_verify/src/resource/memory/intrinsics.rs` resolves calls by compiler identity. `memory/synchronization.rs` checks lookalike types, layouts, disabled lifetime checking and Rust’s guard Send restriction. `synchronization/mutex.rs` checks aliases, blocking reacquisition, poison, failed try-lock and checked unwrap. |
| Publication, waits, completion, join and strong ownership | `workers/waits.rs` and `workers/states.rs` track the waiting actor, completion record and receipt. `worker_execution.rs` checks both spawn APIs, worker preconditions, a failing worker, blocked storage and delayed delivery. `worker_shared_ownership/payloads.rs` checks uniqueness, returned owners and rejection of Weak, raw, leaked and cyclic ownership. `join_waits_reject_cycles_and_resume_only_the_actual_waiting_actor` exercises wait identity. |
| Allocation lifetimes, cleanup and helper composition | `synchronization/lifetimes.rs` and `synchronization/helpers.rs` cover early returns, explicit and implicit drop, guard moves, release in a helper and repeated acquisition. `fixed_workers/composition.rs` checks a buffer surviving unlock and join, nested workers and extra helper workspace. |
| Semaphore, verified RwLock, atomics and custom protocols | `rust_verify/src/resource/memory/protocol.rs` binds holder proofs and measured workspace. The `atomic_lib` tests in `holders.rs`, `rwlock.rs` and `semaphore.rs` check failed CAS, a false holder theorem or capacity, same and different issuers, reader overlap, writer exclusion, release and destruction. `memory/synchronization/atomic.rs` covers both CAS outcomes, checked counter operations and invariant restoration. |
| Symbolic overlap, shared contents and scoped queries | `workers/envelope/` prices fixed subtrees and counted populations from executable publications, joins and compatible phases. `counted_workers.rs` checks zero, one and many workers, early release, different mutexes and overflow. `concurrent_scopes.rs` covers early section exits and current versus peak after join. The public semaphore and custom-lock examples check `min(n, k) * b` and exclusive `b` scratch contributions respectively. |
| Preservation of trust and explicit exclusions | `a_functional_specification_cannot_hide_an_allocation_in_a_worker` rejects an opaque allocating helper. `excluded_concurrency_operations_in_a_worker_fail_at_their_source` exercises channels, condition variables, barriers, scoped threads, relaxed standard atomics, unwinding and async work. `concurrent_exports_wait_for_the_byte_proof_and_erased_rust_checks` checks failed, disabled and partial verification as well as successful export. |

Worker implementation paths beginning with `workers/` are under `source/vir/src/resource/memory/`. The integration tests are in `source/rust_verify_test/tests/`, under `resource/memory/` and `atomic_lib/`.

### Four-worker comparison

In `examples/resource/memory/concurrent/mutex_lifetimes.rs`, all four workers are published before any join. The helper that reserves and drops `b` bytes under the mutex verifies within the operation’s `b + 256` allowance. Moving its call past unlock invalidates that bound. When each successful holder pushes an owning vector into the initially empty shared vector, the after-join checkpoint verifies at **1,177 bytes**. The 57-byte shared cell and handle remain live alongside four 24-byte slots and four 256-byte reservations. Both 337 bytes (one retained buffer) and 1,176 bytes fail at that checkpoint. The whole-operation allowance also covers temporary storage during insertion. In `worker_result.rs`, a completed worker owns its returned buffer while another worker can acquire the mutex and allocate scratch. The verifier accepts `2 * bytes + 256` and rejects `bytes + 256`. All four public examples verified with `--no-cheating`, compiled and ran.

### Compatibility and precision

The shared 64-bit word, integer, array and reference sizing rules predate concurrency. Model revisions v39 and v40 introduced synchronization and worker storage. The separately versioned v41 and v42 changes revised collection accounting; v43 added permissioned atomic operations. Existing sequential layout and memory regressions passed. Prepared runtime queries checked the 36-byte mutex/lock-results formula and 33-byte Arc/join-handle/join-result formula against the static results. A runtime size query on the static-only vstd `PAtomicUsize` was rejected by the sealed layout trait.

The fixed-history search has a documented 128-state limit per mutex. In the audit, two and three helpers that lock and conditionally append verified. Four such helpers exceeded the search limit and left the total unproved even with a 16,000-byte allowance. Four direct guarded appends verified. Indexed owning results and cross-actor joins also retain their documented whole-operation proof restrictions. These limits affect what can be proved within the supported abstraction.

### Validation

The full release memory integration run passed 1,273 tests. Focused runs passed after the final export, exclusion and worker-result test changes. All 51 resource examples, 88 VIR memory tests, 8 frontend memory tests, 592 upstream and protocol regressions, 21 parser/prettyprinter cases and 16 prepared runtime checks passed. One VIR test and eight upstream tests were marked ignored. The implementation commit records the commands. The installed upstream `verusfmt` cannot parse the fork’s `resources` syntax. Workspace Rust formatting, Clippy, whitespace and local documentation link checks passed.
