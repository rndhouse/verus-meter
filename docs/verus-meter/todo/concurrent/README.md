# Concurrent symbolic memory analysis TODOs

These tasks track implementation of the concurrent core.
Next is [05.1 — Shared contents across workers](05.1-shared-contents-across-workers.md).
[05 — Function and worker summaries](05-function-and-worker-summaries.md) tracks the four subtasks and final integration checks. The [final worker audit](complete/03.4.3-validate-and-close-03.md) records the verified worker scope and integration checks.

## Authoritative location

Read, update, move and commit these TODO documents in the `main` branch checkout,
under `docs/verus-meter/todo/concurrent/`. Find the checkout with `git worktree list`.
Implement and validate code in `feature/concurrent-symbolic-analysis`; source paths
in these documents refer to that implementation checkout until its changes merge.
Tracked copies inherited by other worktrees are not authoritative. Leave them in
place without updating or deleting them. Commit code on the implementation branch,
then commit the corresponding completion evidence and document moves on `main`.

## Order

Work in numbered order: after 02, complete 03.1, 03.2, 03.3 and 03.4, then close
the umbrella checklist in 03 before continuing to 04. Each document states
dependencies, required work, completion criteria, validation and source starting
points. The 03 subtasks also name remaining integration obligations. These are
implementation responsibilities within one core feature, not partial releases.
Preserve the semantics and synchronization precision established in 01 throughout.

| Done | TODO | Delivers |
| --- | --- | --- |
| [x] | [01 — Semantics and supported scope](complete/01-semantics-and-supported-scope.md) | Accounting, proof interface, trust boundary and concrete operation matrix. |
| [x] | [02 — Synchronization contracts and identities](complete/02-synchronization-contracts-and-identities.md) | Common representation and trusted standard mutex integration. |
| [x] | [03 — Worker lifetimes and shared storage](complete/03-worker-lifetimes-and-shared-storage.md) | Spawn/join, captures, shared allocations, symbolic populations and retained results. |
| [x] | [03.1 — Closure invocation and cleanup](complete/03.1-closure-invocation-and-cleanup.md) | Semantic invocation and cleanup without exact generated-wrapper requirements. |
| [x] | [03.2 — Executable worker analysis](complete/03.2-executable-worker-analysis.md) | Checked body effects and worker-summary integration through completion/join. |
| [x] | [03.3 — Symbolic populations and shared ownership](complete/03.3-symbolic-populations-and-shared-ownership.md) | Tracks 03.3.0–03.3.3 in order through per-allocation counts, transfers, worker states and final release. |
| [x] | [03.4 — Worker integration and completion](complete/03.4-worker-integration-and-completion.md) | Evidence for all worker requirements and explicit remaining proof boundaries. |
| [x] | [03.4.1 — Audit worker lifetimes](complete/03.4.1-audit-worker-lifetimes.md) | Trace ownership through spawn, waiting, completion and join. |
| [x] | [03.4.2 — Audit loops and shared ownership](complete/03.4.2-audit-loops-and-shared-ownership.md) | Verify worker membership and final release across loop iterations. |
| [x] | [03.4.2.1 — Carry peer-owned allocations through loop iterations](complete/03.4.2.1-carry-peer-backings-through-loops.md) | Account for a backing between separate carrier and peer drains. |
| [x] | [03.4.2.2 — Join a carrier while publishing its peers](complete/03.4.2.2-join-during-peer-publication.md) | Preserve each surviving allocation when publication and collection share a loop. |
| [x] | [03.4.2.3 — Join shared collections in a worker](complete/03.4.2.3-join-shared-collections-in-a-worker.md) | Reconcile fully drained shared handle collections with the publisher. |
| [x] | [03.4.2.4 — Transfer surviving shared ownership](complete/03.4.2.4-transfer-surviving-shared-ownership.md) | Carry remaining handles, returned aliases and per-visit reservations into the next actor. |
| [x] | [03.4.2.5 — Preserve repeated payload ownership](complete/03.4.2.5-preserve-repeated-payload-ownership.md) | Preserve the inner owners of a fresh shared allocation on each visit. |
| [x] | [03.4.2.6 — Extract a joined inner Arc](complete/03.4.2.6-extract-a-joined-inner-arc.md) | Recover the selected inner allocation and release the unique wrapper. |
| [x] | [03.4.2.7 — Track independent inner aliases](complete/03.4.2.7-track-independent-inner-aliases.md) | Keep a loop-created inner backing live through either order of publisher and worker drops. |
| [x] | [03.4.2.8 — Index a worker with a forwarded Arc](complete/03.4.2.8-index-a-worker-with-a-forwarded-arc.md) | Preserve the original allocation visit when a receiving worker enters another handle vector. |
| [x] | [03.4.3 — Validate and close 03](complete/03.4.3-validate-and-close-03.md) | Run integrated checks and reconcile the worker completion criteria. |
| [x] | [04 — Allocation and synchronization lifetimes](complete/04-allocation-and-synchronization-lifetimes.md) | Compiler-derived containment, escape and release relationships. |
| [ ] | [05 — Function and worker summaries](05-function-and-worker-summaries.md) | General helper/lifetime composition and protected payloads, extending 03.2's summaries. |
| [ ] | [05.1 — Shared contents across workers](05.1-shared-contents-across-workers.md) | Connect a mutex release to the contents visible to its next holder. |
| [ ] | [05.2 — Ownership after unlock](05.2-ownership-after-unlock.md) | Account for removed storage through worker completion, join and final drop. |
| [ ] | [05.3 — Helpers and conditional paths](05.3-helpers-and-conditional-paths.md) | Preserve protected updates, ownership and guard effects on each path through a call. |
| [ ] | [05.4 — Repeated acquisitions and loop-selected mutexes](05.4-repeated-acquisitions-and-loop-selected-mutexes.md) | Preserve the selected mutex and its contents across symbolic iterations. |
| [ ] | [06 — Verified protocols and bounded permits](06-verified-protocols-and-bounded-permits.md) | Custom Verus protocols and the selected semaphore interface. |
| [ ] | [07 — Symbolic concurrent bound composition](07-symbolic-concurrent-bound-composition.md) | Tight total bounds, generated proofs and diagnostics. |
| [ ] | [08 — Core integration and completion](08-core-integration-and-completion.md) | Full capability audit, regression coverage and user documentation. |

03.2 brings forward the worker-summary machinery needed to connect actual bodies
and lifecycle effects; it must not defer that connection to 05. TODO 04 adds local
allocation/synchronization lifetime conditions, and 05 extends the common summary
interface across general helpers. 07 owns the global simultaneous-byte proof.

## Requirements that apply to every task

Use the existing symbolic memory analysis. Standard primitives expose trusted or
verified guarantees; custom implementations expose Verus-proved guarantees.
Neither requires users to maintain allocation counters or distribute byte credits.
Always connect those guarantees to executable storage lifetimes.

Use the [source memory accounting rules](../../accounting/README.md) for every
task. Each supported library operation contributes its documented storage
effects. Synchronization constrains which modeled bytes can be live together.
Callers can derive bounds without knowing the library's private allocation strategy.

Compiler-derived capture, move and cleanup facts are compatible with the source
memory model. Normalize useful frontend evidence without requiring a particular
generated closure-wrapper shape or charging physical compiler implementation
storage. Reuse the existing memory analysis; do not build another Rust ownership
checker or reduce concurrent effects to independent worst-case worker peaks.

Keep synchronization-instance identity, acquisition lifetime and allocation
identity distinct. Count all live storage, including blocked workers and retained
results. Unsupported behavior must fail explicitly. Do not accept concurrent
contracts through an incomplete path just because a later TODO will add checks.

Source-connected intermediate tests must exercise the production analysis and
checked obligations. They may inspect results before the global rejection boundary;
they must not disable it or present internal ledger tests as accepted byte proofs.
Each subtask must deliver connected behavior, with focused tests during development
and the applicable full checks once ready. Resolve the next concrete integration
requirement before adding infrastructure without a current consumer.

Read applicable repository instructions, inspect current changes and preserve
unrelated work. Source starting points in numbered documents are repository-root
paths, intentionally independent of whether the document is in `complete/`.

## Core capability coverage

Each owning task supplies the implementation. TODO 08 verifies the evidence across
the [concurrent specification](../../concurrent-model.md) and these capabilities.

| Core requirements | Owning TODOs |
| --- | --- |
| accounting/trust semantics and division of responsibility | 01, 02 |
| standard contracts, guard/permit semantics and capacity effects | 02, 06 |
| automatic lifetime relationships and executable-allocation obligations | 04, 05, 07 |
| symbolic total bounds and exclusive/bounded overlap | 03, 06, 07 |
| worker lifecycle, sharing and ownership conservation | 03.1–03.4 (03 checklist), 04 |
| custom synchronization proofs | 02, 06 |
| helper composition and identity across boundaries | 03.2–03.3 worker foundation, 05 general helpers |
| combined per-holder charges and retained allocations | 02, 03, 04, 07 |
| negative tests, standard/custom integration and regressions | 02–07, 08 |
| explicit support boundary, diagnostics and complete validation | 01, 07, 08 |

## Completing and moving a TODO

1. Complete every required checkbox and completion criterion in that document.
   Run the relevant checks against the implementation. Partial progress stays in
   the active directory; record remaining work in its unchecked items.
2. Review the exact staged implementation and tests. Record meaningful validation
   results in coherent commit messages; keep raw logs in ignored disposable
   locations. Commit according to the repository's instructions.
3. Move the completed document, keeping its numbered filename, into
   `docs/verus-meter/todo/concurrent/complete/`. Update this index's link to
   `complete/<filename>` and mark its row done. Check all affected links.
   For a numbered child, update its link and checkbox in the parent as well.
   Keep the parent active until its subtasks and integration criteria are complete.
   When moving the parent, adjust its links to children already in `complete/`.
4. Record evidence for the complete capability, including dependent integration,
   in its owning TODO. Completing an infrastructure task
   does not by itself complete the corresponding end-to-end capability.
5. Commit the document move and tracking updates in the authoritative `main`
   checkout after committing the implementation on its feature branch. Identify
   the implementation commit and validation evidence when recording completion.
   If later work invalidates completion, move the task back, clear its status and
   reopen affected capability checks.

The last task cannot move until every required core capability is implemented and
validated. Scope changes must be explicit; do not move incomplete requirements
into an unspecified future phase. Routine design choices can be resolved from
the concurrent specification, while material reductions require user agreement.

## Validation

For memory accounting changes, run from `source/` using the pinned toolchain:

```sh
cargo fmt -p vir -- --check
cargo test --release -p vir --lib resource::memory
cargo build --release -p rust_verify
cargo test --release -p rust_verify_test --test resource memory:: -- --test-threads=2
cargo test --release -p rust_verify_test --test examples resource_ -- --test-threads=2
```

Build before integration tests so they execute the changed verifier. Add relevant
parser/prettyprinter and upstream reference, array, mode, erasure, iterator and
function-contract regressions when their boundaries change. Concurrency work
also needs affected atomic/invariant/closure tests. Run formatting and Clippy for
affected Rust packages/targets, and strict rustdoc when public APIs or documentation
lints change. Rebuild and verify vstd when its implementations or contracts change.

Use existing prepared tools; do not provision tools implicitly. Use Rust for test
orchestration. Test distinct behaviors and integration boundaries rather than
mirroring internal records. Repeat checks only after relevant changes, failures
or unresolved concerns. Documentation-only tasks need whitespace and reference
checks; executable documentation examples need focused verification or compilation
appropriate to the claims they make. Report actual results and unresolved gaps.
