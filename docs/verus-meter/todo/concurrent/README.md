# Concurrent symbolic memory analysis TODOs

Implement the [approved plan](../plan-concurrent-symbolic-analysis.md) as one
complete core feature. These tasks divide implementation responsibilities; they
are not separate prototypes or releases. No implementation is marked complete.
The parent plan is the capability checklist; this index tracks the work that
satisfies it. Read both before starting a task.

## Order

Work in numbered order. Each document states dependencies, required work,
completion criteria, validation and source starting points. Resolve semantics
and interfaces together in 01 so later tasks preserve synchronization precision
from their first implementation.

| Done | TODO | Delivers |
| --- | --- | --- |
| [ ] | [01 — Semantics and supported scope](01-semantics-and-supported-scope.md) | Accounting, proof interface, trust boundary and concrete operation matrix. |
| [ ] | [02 — Synchronization contracts and identities](02-synchronization-contracts-and-identities.md) | Common representation and trusted standard mutex integration. |
| [ ] | [03 — Worker lifetimes and shared storage](03-worker-lifetimes-and-shared-storage.md) | Spawn/join, captures, shared allocations, symbolic populations and retained results. |
| [ ] | [04 — Allocation and synchronization lifetimes](04-allocation-and-synchronization-lifetimes.md) | Compiler-derived containment, escape and release relationships. |
| [ ] | [05 — Function and worker summaries](05-function-and-worker-summaries.md) | Precise identities, ownership and synchronization effects across calls. |
| [ ] | [06 — Verified protocols and bounded permits](06-verified-protocols-and-bounded-permits.md) | Custom Verus protocols and the selected semaphore interface. |
| [ ] | [07 — Symbolic concurrent bound composition](07-symbolic-concurrent-bound-composition.md) | Tight total bounds, generated proofs and diagnostics. |
| [ ] | [08 — Core integration and completion](08-core-integration-and-completion.md) | Full capability audit, regression coverage and user documentation. |

## Requirements that apply to every task

Use the existing symbolic memory analysis. Standard primitives expose trusted or
verified guarantees; custom implementations expose Verus-proved guarantees.
Neither requires users to maintain allocation counters or distribute byte credits.
Always connect those guarantees to executable storage lifetimes.

Keep synchronization-instance identity, acquisition lifetime and allocation
identity distinct. Count all live storage, including blocked workers and retained
results. Unsupported behavior must fail explicitly. Do not accept concurrent
contracts through an incomplete path just because a later TODO will add checks.

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
| 7, 8: worker lifecycle, sharing and ownership conservation | 03, 04 |
| 9: custom synchronization proofs | 02, 06 |
| 11, 12: helper composition and identity across boundaries | 03, 05 |
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
4. Update the parent capability checklist only when the complete capability has
   evidence, including dependent integration. Completing an infrastructure task
   does not by itself complete the corresponding end-to-end capability.
5. Commit the document move and tracking updates with the completed work or a
   coherent follow-up commit. If later work invalidates completion, move the task
   back, clear its status and reopen affected parent checklist items.

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
