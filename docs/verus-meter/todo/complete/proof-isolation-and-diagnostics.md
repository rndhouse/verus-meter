# Proof isolation and diagnostics

## Goal and coordination

Make symbolic memory proofs easier to diagnose and less sensitive to unrelated
proof machinery before resuming concurrent TODO 03.3. Preserve the existing
source-level memory model, supported behavior and soundness boundaries.

This file is authoritative in the `main` checkout. Implement in the existing
`feature/concurrent-symbolic-analysis` worktree, starting from the stable
checkpoint `f32a74e7f`. Locate checkouts with `git worktree list`. Do not create or
update a second tracking copy in the implementation worktree.

Work through sections 1–3 in order, using multiple coherent, validated commits.
After each implementation commit, update the relevant checkboxes here with its
commit reference and a concise account of any remaining boundary. Keep detailed
investigation evidence and validation results in commit messages; keep raw logs
in ignored disposable locations. Do not accumulate chronological status reports.

[Concurrent TODO 03.3](../concurrent/complete/03.3-symbolic-populations-and-shared-ownership.md)
remains open. This work does not complete it or enable global concurrent bounds.
Move this file to `docs/verus-meter/todo/complete/` only when all three sections
are resolved, updating relative links when moving it.

## Findings motivating the work

1. Proof-emitter scopes prevent invalid reuse of branch-local facts, but are not
   separate solver queries. Ordinary blocks are flattened during translation.
   `assert … by` limits exported conclusions without necessarily isolating solver
   work. Distinguish cache scope, logical fact scope and solver-query boundaries.
2. Some metadata operations and helper calls activate broad ownership-rule groups.
   A review of the checkpoint's sequential `build` function in the existing
   `ordered_append_blocks_compose_direct_helpers_and_nested_loops` regression
   recorded 13,648 user-level quantifier instantiations. Selection and lookup
   rewrites dominated the profile. The regression passes; this count is a
   measurement target, not proof that every instantiation is unnecessary or a
   fixed performance threshold. A saved earlier failure profile also showed
   extensive ownership-rule instantiation.
3. Summary inference often returns `None`, losing the distinction between an
   unsupported operation, incomplete transition coverage and unclosed symbolic
   inputs. Required summaries then produce one generic error. Some generated
   assertions have useful labels, but generated loop invariants do not retain
   their memory-specific purpose consistently.
4. The common allocation `Record` includes recursive worker observations behind
   specification queries. The reviewed sequential solver input still includes
   that field, while unused worker-query functions are pruned. Logical opacity
   therefore reduces exposure without removing the structural dependency.

The checkpoint's full memory suite passed. This review identifies robustness and
diagnostic work; it does not establish that the current byte semantics need to
change or that a new metadata representation is necessary.

## 1. Explain inference and proof failures

- [x] Preserve actionable failure reasons at summary, loop-composition and
  coverage boundaries, including the relevant source operation or loop. Start
  with those boundaries rather than mechanically replacing every `Option`.
  Preserve legitimate speculative fallback: an inapplicable candidate is not
  necessarily an unsupported program, and optional summaries may remain absent.
- [x] Carry the purpose and source origin of generated obligations through
  instrumentation. Distinguish byte bounds, descriptor validity, ownership
  transport, worker membership and backing-storage bounds, including loop-entry,
  back-edge and exit obligations where applicable.
- [x] Use existing Verus messages, proof notes, assertion identities and logging
  facilities where appropriate. Identify any necessary narrow integration change
  before extending upstream IR. Avoid introducing a parallel diagnostic framework.
- [x] Keep unsupported analysis, failed verification obligations and solver
  resource exhaustion distinguishable. A failed proof alone cannot establish
  whether the proposed relationship is false or supporting facts are missing;
  diagnostics must not claim that distinction without evidence.
- [x] Add focused regressions for distinct inference failures and generated
  obligation labels. Confirm source locations and failure purposes, while
  retaining rejection of unsupported behavior and invalid bounds.

Implementation evidence: `efba6233a` preserves summary-boundary explanations and
terminal loop/checked-operation source locations, retaining speculative fallback
and optional summaries. `b7ac6f98a` labels generated memory invariants and carries
existing Verus proof-note text through loop entry, back-edge, continue and exit
checks. Neither change alters proof formulas or solver limits. Unsupported
analysis, failed obligations and resource exhaustion retain distinct diagnostics;
a failed obligation does not claim to distinguish a false property from missing
supporting facts. Source regressions check inference locations, optional-summary
acceptance and loop labels. Validation includes 1,030 memory regressions, 44
resource examples and 361 upstream regressions; details are in the commits.

Completion: a developer can identify the failed analysis stage or generated
obligation and its source origin without reverse-engineering an entire generated
function. Commit and record this improvement before beginning broad proof changes.

## 2. Reduce what each generated proof must consider

- [x] Establish reproducible baselines using existing tests: ordinary collection
  construction, nested/indexed ownership, helper transfers, retained workers and
  deliberately insufficient bounds. Include the previously sensitive tests
  `ordered_append_blocks_compose_direct_helpers_and_nested_loops`,
  `disjoint_fixed_roles_transfer_nested_children_with_a_symbolic_count` and
  `distinct_indices_preserve_nested_fixed_and_runtime_paths`.
- [x] Record the commit, selected source case/function, verifier and solver
  configuration, query outcomes and relevant profiling measurements. Reuse
  Verus profiling and AIR/SST logs, plus the test runner's `VERUS_TEST_LOG_DIR`,
  `VERUS_KEEP_TEST_DIR` and `VERUS_EXTRA_ARGS` facilities. Account for the logging
  helper recording only the first invocation of a multi-case test.
- [x] Audit broad rule activation in metadata locals and helper transfers. For
  each selected proof family, identify the required inputs and exported
  conclusions; replace unnecessary broad automation with targeted lemma calls
  or locally scoped rule activation. Change one proof family per reviewable step.
- [x] Keep construction validation, collection transport and byte accounting
  separate. Carry worker descriptions unchanged through transport; inspect them
  only when their properties are needed. Reuse the shared loop transformation
  for both exit summaries and membership invariants.
- [x] Use existing verified proof helpers and `assert … by` boundaries to expose
  only necessary conclusions. Do not assume an AST block or fresh emitter creates
  a solver boundary. If a genuinely separate query is needed, justify the smallest
  integration with Verus and prove its assumptions at the originating source site.
  Do not switch solver modes merely to obtain query separation.
- [x] Compare the same representative cases before and after each change. Require
  evidence of reduced solver work or removed unnecessary proof dependencies,
  alongside unchanged verification behavior. Do not optimize for an exact
  quantifier count or fix a timeout by increasing resource limits.

Implementation evidence: `204509748` narrows selection through removed subtrees,
the proof family selected for this pass. Construction no longer activates
`select_without` merely by creating metadata; projections and helper transfers
retain it for later sibling views. Existing construction validation, opaque
worker transport and byte proofs remain separate. No new solver-query mechanism
is introduced; the fact-cache comment now states its actual scope. Other lookup
and collection rules remain unchanged.

The baseline is `b7ac6f98a`, with 19 existing regressions covering construction,
nested indices, disjoint helper transfers, retained workers and negative bounds.
The same cases pass within the final 1,030-test memory suite. The selected
`direct_block` / `build` profile changes from 13,648 to 12,871 user-level
instantiations, with the subtree-cut rule inactive in that query. This is a
bounded reduction in proof dependencies, not a general speedup claim. The commit
records source selection, pinned tools, verifier flags and profiling limitations;
concurrent profiles sharing a solver-log directory were excluded from numerical
comparisons. VSTD proofs, unit tests, examples, formatting and Clippy also pass.

Completion: the selected proof families have explicit responsibilities and
controlled supporting facts, with measured improvement and no regression in the
affected positive or negative cases. Fix misleading isolation comments as part
of the relevant change. A wholesale proof-engine rewrite is outside this task.

## 3. Reassess the shared worker-metadata representation

- [x] After sections 1–2, inspect sequential and concurrent solver inputs to
  determine which worker dependencies remain and whether they cause material
  proof cost or instability. Separate dependency evidence from conjectures about
  solver sensitivity.
- [x] Compare retaining the current query-based representation with separating
  worker descriptions from ordinary allocation records. Evaluate the impact on
  exact occurrence identity, immutable capture/result observations, helper
  substitution and collection membership; a byte-only view is insufficient.
- [x] Record a decision and its evidence. Keeping the current representation is
  a valid completion outcome if the disruption of separation is not justified.
  Do not leave an unbounded redesign as an implicit follow-up.
- [x] If separation is justified, define its bounded scope and acceptance checks
  here before implementing it. Preserve source-derived construction, transfer,
  join and destruction obligations, and validate the resulting change in coherent
  commits. If separation is unnecessary, mark this item not applicable with the
  decision reference.

Decision: retain the current query-based representation; no separation is needed
for this refactoring task. Inspection after `204509748` finds the worker field in
sequential AIR, but no worker observation/result/membership query functions in
the selected construction query. The retained-worker query includes those
functions as expected; its profile is led by ordinary view-request and sequence
rules and still reaches the mandatory global concurrency rejection. These
observations do not prove that the field has zero cost, but do not establish a
material representation bottleneck that warrants a rewrite.

Keeping observations on the record preserves occurrence identity and immutable
capture/result data through the same path transformations, helper substitution
and collection membership proofs. A separate representation would need a checked
correspondence between allocation records and worker descriptions at all those
boundaries; a byte-only view cannot supply it. The present evidence favors the
smaller design. The conditional separation item above is therefore not applicable.
This closes the representation review without scheduling an implicit redesign;
03.3 remains responsible for the outstanding concurrency functionality.

Completion: the representation decision is explicit. Any adopted change is
implemented and validated; otherwise the documented decision closes this section.

## Safeguards and validation

- Preserve symbolic byte bounds, source allocation/lifetime semantics and the
  existing mandatory global concurrency rejection. Do not add user-maintained
  ghost counters, credits, assumptions or new requirements to make existing
  programs verify.
- Preserve accepted programs and meaningful negative cases. Oversized executable
  allocations, incorrect bounds and discarded outstanding workers must still
  fail for the intended reason. Diagnostics may improve; tests must not be
  weakened to accept unrelated errors or resource exhaustion.
- Keep proof dependencies checked and complete. Scope-local facts cannot escape
  without proof, unsupported ownership cannot become a byte-only summary, and
  collection transport cannot assert worker completion or release live storage.
- For implementation commits, follow applicable `AGENTS.md` checks. Build the
  verifier before integration tests and verify changed VSTD proofs. Run focused
  regressions during development and the required full memory checks at stable
  checkpoints; include appropriate formatting, Clippy and strict documentation
  checks for affected code. Record actual results and any gaps in the commit.
- Do not add brittle tests of generated names, exact solver counts or incidental
  IR layout. Use behavior and meaningful proof boundaries as regression targets.

## Starting points

Directories below are relative to the implementation branch's repository root.

- Inference and evidence, under `source/vir/src/resource/memory/`:
  `transfer/mod.rs`, `transfer/trace.rs`, `transfer/trace/loops/prefixes.rs`,
  `analysis.rs`.
- Proof generation, under `source/vir/src/resource/memory/transfer/`:
  `proofs.rs`, `proofs/scope.rs`, `proofs/builders.rs`, `proofs/prefixes.rs`.
- Instrumentation and rule activation, under `source/vir/src/resource/memory/`:
  `metadata.rs`, `metadata/expr.rs`, `transfer/calls.rs`,
  `loops/analysis/visits.rs`, `symbolic.rs`.
- Metadata algebra, under `source/vstd/std_specs/resource/memory/`:
  `forest.rs`, `groups.rs`, `selection.rs`, `references.rs`.
- Verus integration, under `source/vir/src/`: `ast_to_sst.rs`, `sst_to_air.rs`,
  `prune.rs`; under `source/rust_verify/src/`: `config.rs`, `verifier.rs`.
- Regression cases, under `source/rust_verify_test/tests/resource/memory/`:
  `loop_ownership.rs`, `indexed_loops.rs`, `worker_populations.rs`.
  Logging support: `source/rust_verify_test/tests/common/mod.rs`.
