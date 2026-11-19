# Concurrent symbolic memory analysis TODOs

Implement the [approved plan](../plan-concurrent-symbolic-analysis.md) as one
complete core feature. These tasks divide implementation responsibilities; they
are not separate prototypes or releases. TODOs 01–02 and 03.1–03.3 are complete. Next is
[03.4 — Worker integration and completion](03.4-worker-integration-and-completion.md).
The parent plan is the capability checklist; this index tracks the work that
satisfies it. Read both before starting a task.

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
| [ ] | [03 — Worker lifetimes and shared storage](03-worker-lifetimes-and-shared-storage.md) | Spawn/join, captures, shared allocations, symbolic populations and retained results. |
| [x] | [03.1 — Closure invocation and cleanup](complete/03.1-closure-invocation-and-cleanup.md) | Semantic invocation and cleanup without exact generated-wrapper requirements. |
| [x] | [03.2 — Executable worker analysis](complete/03.2-executable-worker-analysis.md) | Checked body effects and worker-summary integration through completion/join. |
| [x] | [03.3 — Symbolic populations and shared ownership](complete/03.3-symbolic-populations-and-shared-ownership.md) | Tracks 03.3.0–03.3.3 in order through per-allocation counts, transfers, worker states and final release. |
| [ ] | [03.4 — Worker integration and completion](03.4-worker-integration-and-completion.md) | Evidence for all worker requirements and explicit remaining proof boundaries. |
| [ ] | [04 — Allocation and synchronization lifetimes](04-allocation-and-synchronization-lifetimes.md) | Compiler-derived containment, escape and release relationships. |
| [ ] | [05 — Function and worker summaries](05-function-and-worker-summaries.md) | General helper/lifetime composition and protected payloads, extending 03.2's summaries. |
| [ ] | [06 — Verified protocols and bounded permits](06-verified-protocols-and-bounded-permits.md) | Custom Verus protocols and the selected semaphore interface. |
| [ ] | [07 — Symbolic concurrent bound composition](07-symbolic-concurrent-bound-composition.md) | Tight total bounds, generated proofs and diagnostics. |
| [ ] | [08 — Core integration and completion](08-core-integration-and-completion.md) | Full capability audit, regression coverage and user documentation. |

03.2 brings forward the worker-summary machinery needed to connect actual bodies
and lifecycle effects; it must not defer that connection to 05. TODO 04 adds local
allocation/synchronization lifetime conditions, and 05 extends the common summary
interface across general helpers. 07 owns the global simultaneous-byte proof.
The parent plan's supported scope and acceptance requirements remain unchanged.

## Requirements that apply to every task

Use the existing symbolic memory analysis. Standard primitives expose trusted or
verified guarantees; custom implementations expose Verus-proved guarantees.
Neither requires users to maintain allocation counters or distribute byte credits.
Always connect those guarantees to executable storage lifetimes.

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

## Coverage of the parent checklist

The numbers below refer to the 20 checklist entries in their current order in the
approved plan. Descriptions keep the mapping understandable if entries are added.
An owning task supplies the implementation; 08 verifies the evidence for all items.

| Parent requirements | Owning TODOs |
| --- | --- |
| 1, 4: accounting/trust semantics and division of responsibility | 01, 02 |
| 2, 3: standard contracts, guard/permit semantics and capacity effects | 02, 06 |
| 5, 15: automatic lifetime relationships and executable-allocation obligations | 04, 05, 07 |
| 6, 10: symbolic total bounds and exclusive/bounded overlap | 03, 06, 07 |
| 7, 8: worker lifecycle, sharing and ownership conservation | 03.1–03.4 (03 checklist), 04 |
| 9: custom synchronization proofs | 02, 06 |
| 11, 12: helper composition and identity across boundaries | 03.2–03.3 worker foundation, 05 general helpers |
| 13, 14: combined per-holder charges and retained allocations | 02, 03, 04, 07 |
| 16, 17, 18: negative tests, standard/custom integration and regressions | 02–07, 08 |
| 19, 20: explicit support boundary, diagnostics and complete validation | 01, 07, 08 |

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
   This also applies individually to 03.1–03.4: update the links and rows in 03
   when a subtask moves. Keep 03 active until all its criteria and subtasks are
   complete; when moving 03, adjust its relative links to the completed subtasks.
4. Update the parent capability checklist only when the complete capability has
   evidence, including dependent integration. Completing an infrastructure task
   does not by itself complete the corresponding end-to-end capability.
5. Commit the document move and tracking updates in the authoritative `main`
   checkout after committing the implementation on its feature branch. Identify
   the implementation commit and validation evidence when recording completion.
   If later work invalidates completion, move the task back, clear its status and
   reopen affected parent checklist items.

The last task cannot move until every required core capability is implemented and
validated. Scope changes must be explicit; do not move incomplete requirements
into an unspecified future phase. Routine design choices can be resolved from
the approved plan, while material reductions require user agreement.

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
