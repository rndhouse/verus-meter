# 03. Worker lifetimes and shared storage

Dependencies: 01–02. All code paths below are relative to the repository root.

## Goal

Account for all supported worker and shared-storage lifetimes without losing or
multiplying allocation charges. Connect actual worker execution to checked
ownership and effect descriptions for later synchronization-aware composition.
Spawning must never be handled as a completed ordinary function call.

This document is the completion checklist for 03. Implement the remaining work in
03.1–03.4; these are parts of the complete core, not separate feature releases.
Keep 03 open until all four documents and the criteria below are complete.

## Architecture and boundaries

Use the existing symbolic memory analysis for allocation sizes, ownership and
release. Compiler-derived types, captures, control flow and destructor events are
valid evidence for Rust source semantics. They do not add compiler-generated
frames, optimized stack layouts or other physical costs to the memory model.
Replace the requirement for one exact generated FnOnce wrapper shape with semantic
invocation rules that preserve ownership, result transport and cleanup.

Carry allocation identities, synchronization instances, individual acquisitions
and worker occurrences as distinct identities through the connected analysis.
Preserve branches, ordering, construction-time inputs and surviving ownership in
checked effects; do not collapse worker behavior to an independent scalar peak.
Shared storage has one backing charge, including when several workers refer to it.

03.2 owns the worker-summary foundation needed to analyze bodies and connect
publication, execution, completion and join. It must not postpone that connection
to 05. TODO 04 derives allocation-to-synchronization lifetime relationships; 05
extends the same summaries for general helper composition and protected payloads;
07 proves the total concurrent envelope under interference. These later obligations
remain explicit, and no incomplete path may accept a concurrent byte contract.

## Existing foundations

The following have internal or sequential integration coverage. Their completion
does not establish checked concurrent worker execution or a total byte bound.
Preserve their semantic requirements while integrating or simplifying the code.

- [x] Recognize selected native/vstd thread and strong Arc operations by compiler
  identity, retaining functional postconditions and Rust transfer checks without
  assuming successful join. Bind executable calls to their body and control-flow
  sites, retaining loop context without treating a static site as a worker count.
- [x] Recover executable captures after proof erasure and restore native effects
  hidden by logical identity translation. Keep worker dependencies separate from
  ordinary calls, including recursion checks.
- [x] Account for move-closure construction/destruction, partial captures and
  runtime copies, including nested captures. Construction does not execute the
  body. Retain the source definition and disjoint capture views into one inline
  environment instead of duplicating its storage.
- [x] Preserve construction-time scalar and collection-geometry observations
  through closure transport. Repeated constructions still need occurrence binding.
- [x] Maintain internal publication, running, completion, waiting and collection
  states; retain captures/results separately from handles. Internal checks reject
  lost storage, detached/outstanding work and self/cyclic waits.
- [x] Maintain a canonical strong-root ledger and sequential native Arc operations,
  including receiver-temporary lifetimes. Moves and analysis snapshots do not
  clone handles; an owned root is released only at its final strong destruction.
- [x] Preserve shared/worker identities in allocation forests and prove symbolic
  multiplicity laws. Keep publication families distinct from occurrences and
  nested-parent identities; zero-byte links still carry ownership information.
- [x] Derive imported worker views from actual fixed captures without copying
  backing storage. A local final release does not prove global reclamation.

03.1 replaced exact FnOnce adapter validation with source receiver and cleanup
semantics, including checked capture ownership at the invocation boundary.
03.2 connects fixed worker bodies to the existing memory pass, common checked
effects and ownership templates, capture cleanup, and native/vstd join results.
Source tests exercise generated local obligations while the mandatory global
rejection remains. Symbolic populations and global shared lifetimes remain in
03.3; internal transition tests cannot substitute for that source integration.

## Remaining work

| Done | Task | Required result |
| --- | --- | --- |
| [x] | [03.1 — Closure invocation and cleanup](complete/03.1-closure-invocation-and-cleanup.md) | Source-semantic invocation, ownership transport and cleanup without exact generated-wrapper admission checks. |
| [x] | [03.2 — Executable worker analysis](complete/03.2-executable-worker-analysis.md) | Actual worker bodies produce checked effects connected to entry, completion and native/vstd join. |
| [ ] | [03.3 — Symbolic populations and shared ownership](03.3-symbolic-populations-and-shared-ownership.md) | Executable spawn/join loops, nested workers, retained results and global strong ownership have checked symbolic transitions. |
| [ ] | [03.4 — Worker integration and completion](03.4-worker-integration-and-completion.md) | All worker requirements below have source-connected evidence and explicit rejection boundaries. |

## Completion criteria

- [x] Both standard and vstd spawn/join use checked bodies for concrete move
  closures, including supported captures, results and source control flow.
- [ ] Closure construction, spawn setup/publication overlap, execution, waiting,
  completion and joining preserve all modeled inline and separately owned storage.
  Returning storage stays charged until collection; join transfers it once.
- [ ] Capture scalar values, aggregate projections, allocation identities and
  synchronization relationships survive construction, calls and thread boundaries.
  `Send`/`Sync` remain enforced and supply no exclusion or memory allowance.
- [ ] Symbolic loops describe actual historical spawns, outstanding workers and
  retained results, including zero iterations, partial joins and repeated capture
  construction. Generated count/ownership obligations follow executable events.
- [ ] Acyclic nested worker trees, handle transfers and waits preserve actor and
  parent identity. Join-safety obligations cover symbolic families and caller
  substitutions; every accounting scope retains or joins its descendants.
- [ ] Strong Arc operations work across workers, supported runtime containers and
  checked input/output descriptors. Count backing/control storage once and each
  handle separately; prove final release globally. Preserve protected payload
  identity for the owning-payload operations completed in 05.
- [ ] Completion records are allocated at publication. Panic-free worker proofs,
  environmental assumptions and primitive Result outcomes follow 01; native join
  success is never an unproved assumption. Reject detach, scoped borrowed captures,
  Weak/raw/cyclic ownership, leaks and other excluded operations explicitly.
- [ ] All four subtasks are validated and moved to `complete/`. Update their links
  here and in the index as they move. No internal ledger, manually maintained
  ghost counter or unconnected summary can discharge a source memory guarantee.

## Validation

Each subtask requires source-connected regression tests as well as focused internal
tests where useful. Test no workers, symbolic spawn loops, delayed/partial joins,
owned results, shared-root aliases, nested workers and blocked storage. Mutate
executable allocation, transfer and drop operations to check that generated
obligations change. Do not validate only hand-constructed ledger transitions.

Until 04–07 supply the remaining lifetime, protocol and envelope obligations,
source-driven tests may validate checked intermediate effects before the rejection
boundary. They must use the production analysis and must not bypass that boundary
to accept a resource contract. TODOs 07–08 validate total bounds, including the
mutex scratch reduction and too-small bounds. Run the README's applicable checks;
record results in implementation commits rather than a running status diary.

## Decisions from TODO 01

The scope and source costs in `docs/verus-meter/concurrent-model.md` are unchanged.
03.1–03.4 redistribute implementation work, including the necessary worker-summary
foundation formerly deferred to 05. They do not defer a required worker capability
to an unspecified later version or broaden the supported Rust surface.

## Starting points

- `source/vir/src/resource/memory/workers.rs`
- `source/vir/src/resource/memory/workers/body.rs`
- `source/vir/src/resource/memory/closures.rs`
- `source/vir/src/resource/memory/shared.rs`
- `source/vir/src/resource/memory/summary.rs`
- `source/rust_verify/src/resource/memory/concurrency.rs`
- `source/rust_verify_test/tests/resource/memory/concurrency.rs`
