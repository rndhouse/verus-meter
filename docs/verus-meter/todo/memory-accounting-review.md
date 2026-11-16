# Memory accounting correctness review

This tracker covers development correctness review of our own unreleased,
experimental Verus fork. Describe findings by their incorrect behavior, affected
cases, and development impact, without severity ratings.

Review the [memory model](../model.md): an accepted contract must bound all
simultaneous storage charged by that model. Focus on fork-specific memory
accounting; the completed checks do not establish exhaustive correctness.

## Core guarantee checklist

For every permitted execution, modeled live storage must be no greater than
accounted storage, which must be no greater than the declared bound. Verus checks
the generated mathematical obligations; the fork must connect those obligations
to executable behavior under the [documented model](../model.md) and ordinary
Verus trust assumptions. The guarantee concerns model bytes, not physical RAM.

These broader audits remain open. Completed bounded passes below supply evidence
for particular cases; their checked boxes do not close these whole areas.

- [ ] Source interpretation and supported-operation boundaries: preserve moves,
  copies, ignored values, evaluation order, and executable/proof boundaries during
  lowering and erasure. Identify intrinsics by compiler identity, apply the
  documented layout policy, and reject unsupported operations instead of assigning
  zero cost. Start with [frontend intrinsics](../../../source/rust_verify/src/resource/memory/intrinsics.rs),
  `layout.rs`, and `execution.rs`.
- [ ] Ownership, lifetimes, and simultaneous storage: retain charges until their
  modeled lifetimes end; preserve allocation identity across moves and partial
  moves; include replacement overlap; and apply branch and exit cleanup only to
  the executed path. Start with [accounting](../../../source/vir/src/resource/memory/accounting.rs),
  `lifetime.rs`, `heap.rs`, and `control.rs`.
- [ ] Call and loop composition: overlap callee allowances, including declared
  slack, with retained caller allocations; preserve consumed and returned owners;
  and prove loop entry, every back edge, accumulation, and exit behavior. Start
  with [calls](../../../source/vir/src/resource/memory/calls.rs), `ownership.rs`,
  and [loop analysis](../../../source/vir/src/resource/memory/loops/analysis.rs).
- [ ] Ownership metadata agrees with execution: descriptors and simplification
  preserve allocations, charged bytes, capacities, logical child counts, and
  original input regions. Verify the mathematical helper lemmas and establish
  their preconditions at every generated use. Start with
  [transfer machinery](../../../source/vir/src/resource/memory/transfer/mod.rs),
  `metadata/`, and the [ownership-forest library](../../../source/vstd/std_specs/resource/memory/mod.rs).
- [ ] Proof generation and verification integration: emit every required
  inequality as an assertion at the correct execution point, preserve it through
  annotation erasure, and prove generated loop invariants. Check branch guards,
  snapshot/update ordering, arithmetic ranges, and verification selection/bypass
  behavior so unchecked obligations cannot establish a memory guarantee. Start
  with [instrumentation](../../../source/vir/src/resource/memory/symbolic.rs),
  `contracts.rs`, and [pipeline integration](../../../source/rust_verify/src/resource/memory/pipeline.rs).
- [ ] Runtime-query agreement: generated queries evaluate the verified allowance
  with the same arguments, size policy, arithmetic, and helper specialization;
  preserve errors and artifact/model agreement. Runtime decisions still require
  execution preconditions and completed verification. Start with
  [query generation](../../../source/builtin_macros/src/resource/runtime/mod.rs),
  the [runtime evaluator](../../../source/verus-meter/runtime/src/expression.rs),
  and the [shared size policy](../../../source/verus-meter/model/src/lib.rs).

Prioritize proof generation and pipeline integration next, then agreement between
ownership metadata, runtime collections, and loop summaries. Define one invariant
and a bounded scope per pass; inspect its source, calculate independent passing
and failing bounds across relevant contexts, and record fixes, validation, and
remaining questions before marking that scoped work complete.

## Completed bounded passes

- [x] Heap ownership and peak accounting: moves, drops, nested allocations,
  replacement overlap, branch joins, and lexical exits.
- [x] Function and loop composition: retained caller allocations, declared slack,
  returned ownership, accumulating iterations, branches, and early exits.
- [x] Contract and query consistency: unsupported operations, generated proof
  obligations, verification configuration, and agreement between runtime queries
  and verified contracts.
- [x] Validate the initial fixes and commit the completed work.

## Release and transfer invariants

This pass checks the operations that end charges, rather than marking entire
modules reviewed. A checked invariant needs source inspection and independently
calculated passing/failing bounds across its relevant execution contexts.

- [x] Sample named values and fixed children: moves preserve allocation identity;
  replacement charges old and new storage before retiring the old owner.
  Inspected `lifetime.rs`, `children.rs`, `heap.rs`, and `construction.rs`.
- [x] Sample alternatives and exits: a release applies only to its executed path;
  patterns, scope cleanup, returns, breaks, and continues preserve other owners.
  Inspected `values.rs`, `control.rs`, `sections.rs`, and branch accounting.
- [x] Sample runtime collections: extraction, insertion, and indexed replacement move
  child charges without losing backing storage or sibling allocations.
  Inspected `extraction.rs`, `elements.rs`, `boxed_slices.rs`, and `provenance.rs`.
- [x] Sample calls and repeated execution: consumed/returned input regions and retained
  caller storage remain consistent through helper summaries and loop exits.
  Inspected `calls.rs`, `ownership.rs`, `transfer/calls.rs`, and `loops/analysis.rs`.
- [x] Validate the confirmed finding, record remaining limits, and commit this pass.
- [ ] Complete exhaustive coverage of every release/transfer site; defer until
  the review strategy is revised.

This pass ended at the user's request. The inventory and 19 independently
calculated passing/one-byte-short bound pairs covered drops, helper consumption,
collection extraction, replacement overlap, branches, loops, and section returns.
They support the sampled checks above; broader coverage remains unfinished.

## Findings and fixes

### Skipped short-circuit operands released live storage

Before the fix, `flag && { drop(first); true }` and its `||` counterpart could
release a 64-byte box unconditionally in the accounting model. A subsequent
64-byte box then verified under an 80-byte allowance, although the skipped path
kept both payloads live. Passing the box to a consuming helper had the same flaw.

[`analysis.rs`](../../../source/vir/src/resource/memory/analysis.rs) now uses the
existing branch accounting for short-circuit alternatives, rejecting conditional
consumption of enclosing heap owners. The shared branch implementation in
[`lifetime.rs`](../../../source/vir/src/resource/memory/lifetime.rs) evaluates the
unconditional condition before protecting owners for either alternative.
Regressions in
[`control_flow.rs`](../../../source/rust_verify_test/tests/resource/memory/control_flow.rs)
cover both operators, direct drops, consuming calls, guarded local allocations,
retained storage, and unconditional left-operand transfers. Resolved and validated.

### Custom size-trait implementations returned inconsistent runtime allowances

Before the fix, a safe downstream `ValueSize` implementation returning zero made
a generated query report zero for `value_size(Buffer)`, while Verus checked the
same contract as 64 bytes. The query used the downstream byte constant while the
verifier used the struct's modeled layout.

[`layout.rs`](../../../source/verus-meter/runtime/src/layout.rs) now seals
`ValueSize` and `ReferenceSize`, preserving the existing supported types while
preventing downstream byte-count implementations. Compile-fail doctests cover
both traits; the original generated-query reproduction is covered by
[`regressions.rs`](../../../source/verus-meter/runtime/tests/query/regressions.rs).
Validated by eight runtime unit tests, three doctests, and all 12 compiled query
tests, including runtime bundle refresh, relocation, and a Cargo client.

### Wildcard patterns released ignored owners

Matching a stored `Option<Box<_>>` with `_` or `Some(_)` does not move its owner.
A temporary match input also survives through its arm body. Previously,
[`values.rs`](../../../source/vir/src/resource/memory/values.rs) released ignored
allocations at pattern entry, accepting an 80-byte allowance while two 64-byte
payloads remained live. A temporary-input case similarly verified at 90 bytes.

Owning wildcard patterns now fail explicitly; named bindings retain their
existing move and arm-exit cleanup behavior. Removed the corresponding erroneous
discard transition from ownership summaries. Regressions in
[`pattern_ownership.rs`](../../../source/rust_verify_test/tests/resource/memory/pattern_ownership.rs)
cover stored/temporary inputs, nesting, fields, helpers, loops, and an independent
81-byte passing/80-byte failing bound for a named binding. Resolved and validated.

All three confirmed findings are resolved. No additional confirmed findings in
the sampled call/loop composition paths.
Detailed reproduction and validation evidence belongs in the fix commits.
Existing unrelated documentation moves are outside this review.

## Validation

Checks passed against the rebuilt verifier and refreshed runtime bundle:

- Memory unit tests: 41 passed; one manual proof-generation measurement ignored.
- Latest memory integration run: 899 passed; one existing loop test failed on an
  additional solver resource-limit diagnostic and passed unchanged on focused
  retry. Both new pattern regression tests passed, bringing coverage to 900 tests.
- Resource examples: 44 passed.
- Runtime: eight unit tests, three doctests, and 12 compiled query tests passed.
- Formatting for `vir`, `rust_verify_test`, and `verus_meter_runtime` passed.
- Clippy for `vir --lib`, `rust_verify_test --test resource`, and
  `verus_meter_runtime --all-targets` passed.
- Runtime rustdoc with `RUSTDOCFLAGS='-D warnings'`, whitespace checks, and review
  document references passed.

The second pass rebuilt the verifier and reran memory unit tests, integrations,
resource examples, formatting, and Clippy for `vir` and the resource test target.
The earlier runtime checks were unaffected by its changes. One supplemental
one-byte-short delegated-extraction loop probe needed `--rlimit 100` to obtain
the intended budget failure; its passing bound succeeded at the default limit.
Solver-limit sensitivity remains a verification robustness concern for a future
review; no bound violation was accepted in these supplemental pairs.

## Discarded-expression review

- [x] Inspect discarded results and partial moves in `analysis.rs`, `lifetime.rs`,
  `construction.rs`, `places.rs`, `heap.rs`, `children.rs`, and `extraction.rs`;
  follow cleanup through `control.rs` and `sections.rs`, and call composition
  through `calls.rs` and transfer tracing (`evaluation.rs`, `places.rs`, and
  `operations.rs`). Check frontend `ExprOrPlace::unused` distinguishes copies
  from moves and wraps non-unit expression results in temporary places.
- [x] Add eight independently calculated passing/one-byte-short pairs in
  [`lifetimes.rs`](../../../source/rust_verify_test/tests/resource/memory/lifetimes.rs).
- [x] Finish broad validation and commit this bounded pass.

The invariant is that statement cleanup releases only the discarded result's
tree. A partial move keeps the parent's inline storage and sibling allocations;
callee profiles preserve surviving original inputs after a discarded field.
No new incorrect acceptance was found in these samples; no accounting source
change was needed.

| Case | Passing / failing bound (bytes) | Independent peak calculation |
| --- | --- | --- |
| Discarded field, directly and through a helper | 208 / 207 each | 16-byte parent slot + 64-byte surviving payload + 128-byte workspace |
| Discarded factory result, directly, through a block, and in a section | 200 / 199 each | 72-byte retained box + 128-byte workspace |
| Discarded factory result in either branch or two loop iterations | 201 / 200 each | Same 200 bytes + Boolean input or loop counter |
| Discarded owning value from a single-visit break | 200 / 199 | Same retained box and workspace; loop result has ended |

The factory declares 104 bytes, including slack over its 96-byte scratch peak;
that allowance overlaps the retained caller box but stays below the later
workspace peak. Both the loop result's 32-byte payload and its 8-byte handle end
before that workspace. The focused lifetime suite passes all 15 tests.

Validation against the rebuilt verifier: 904 memory integration tests and all 44
resource examples passed without retries. Memory unit tests passed 41 tests with
one existing manual measurement ignored. Formatting for `vir` and
`rust_verify_test`, Clippy for `rust_verify_test --test resource`, whitespace
checks, and all nine tracker links passed. Only tests and this tracker changed;
the accounting and runtime-query implementations were not modified.

Remaining coverage: nested runtime-collection results, partial moves on separate
early-exit paths, and effectful later operands while an earlier result is pending
were not newly probed here. The earlier runtime-query evidence is unchanged;
this pass did not revisit query evaluation. Exhaustive release-site coverage and
the previously recorded solver-limit sensitivity remain open. Existing unrelated
documentation moves remain outside this pass.

## Argument-evaluation overlap review

- [x] Follow pending inline values and allocation trees through `calls.rs`,
  `lifetime.rs`, `accounting.rs`, and `ownership.rs`. Inspect prepared metadata
  and original-input lifetimes in `transfer/calls.rs`, `transfer/origins.rs`, and
  `transfer/trace/operations.rs`, with the selection and effect guards in
  `transfer/mod.rs`, `projections.rs`, `growth.rs`, and `vector_calls.rs`.
- [x] Add 17 independently calculated passing/one-byte-short pairs and one
  unsupported-boundary check in
  [`argument_ownership.rs`](../../../source/rust_verify_test/tests/resource/memory/argument_ownership.rs).
- [x] Complete broad validation and commit this bounded pass.

Earlier arguments retain their inline charges and allocation trees while later
arguments execute. `calls.rs` releases parameter values only after all argument
evaluation, then composes the callee's allowance and input-lifetime profiles.
Branch snapshots retain unnamed pending charges. Both native summaries and the
prepared collection interface preserve returned owners and release consumed
owners independently. No new incorrect acceptance was confirmed in these samples;
the accounting implementation is unchanged.

| Cases | Passing / failing bound (bytes) | Independent peak calculation |
| --- | --- | --- |
| Consume, forward then drop, nested forwarding, later owning result consumed, and incoming helper consumption | 240 / 239 each | Retained caller box 40 + pending argument 72 + later workspace 128 |
| Caller branch, later-argument branch, repeated caller loop, and later loop helper | 241 / 240 each | Same 240 + Boolean input or caller/helper counter |
| Forwarded result retained, with unit or owning later result | 304 / 303 each | Retained caller box 40 + returned box 72 + later scratch 192 |
| Later helper's declared slack | 272 / 271 | 40 + 72 + declared allowance 160, despite only 128 used |
| Incoming helper result or collection result retained | 328 / 327 each | Returned box 72 + scratch 256; or caller box 40 + returned collection 96 + scratch 192 |
| Later argument drops a different incoming owner | 200 / 199 | Pending box 72 + workspace 128; the other box has ended |
| Pending partial move | 248 / 247 | Parent slot 16 + pending handle 8 + both payloads 96 + workspace 128 |
| Pending collection consumed | 264 / 263 | Caller box 40 + collection handle/backing/child 96 + workspace 128 |

The collection cases exercise required prepared transfer metadata. Current-memory
checks additionally verify post-call release of consumed and explicitly dropped
results. A loop written directly inside a later argument is rejected even under
a generous allowance: `growth.revision()` also observes scalar loop proof
instrumentation, triggering the existing vector-allocation-change guard. The
equivalent checked loop helper passes at 241 bytes and fails at 240. This
conservative support boundary is recorded separately from successful byte proofs.
All nine focused tests pass.

Validation against the rebuilt verifier: all 913 memory integration tests and 44
resource examples passed without retries. Memory unit tests passed 41 tests with
one existing manual measurement ignored. Formatting for `vir` and
`rust_verify_test`, Clippy for `rust_verify_test --test resource`, whitespace
checks, and all ten tracker links passed. This pass changes only tests and this
tracker; runtime-query implementation and its prior validation are unchanged.

Remaining coverage: partial moves across distinct early-exit paths and deeper
nested runtime-collection results remain unfinished. This pass does not establish
general equivalence of prepared metadata and execution, revisit runtime-query
evaluation, or resolve the previously recorded solver-limit sensitivity.
Unrelated documentation moves remain outside this pass.

## Partial moves and early exits

- [x] Follow field detachment and exit cleanup in `children.rs`, `lifetime.rs`,
  `control.rs`, and `heap.rs`; match bindings in `values.rs`; and restored parent
  charges in `sections.rs` and `accounting.rs`. Check caller profiles/adoption in
  `calls.rs` and `ownership.rs`. Inspect loop edge classification/consumption in
  `loops/exits.rs` and `loops/analysis.rs`, and symbolic exit cleanup in
  `transfer/trace/{evaluation,exits,branches,patterns}.rs`.
- [x] Add 15 independently calculated passing/one-byte-short pairs in
  [`exit_ownership.rs`](../../../source/rust_verify_test/tests/resource/memory/exit_ownership.rs),
  including current-memory checks after break, continue, return, and drop.
- [x] Finish broad validation and commit this bounded pass.

A partial move leaves the parent's inline slot charged and detaches only the
selected child's allocation tree. Exit results are evaluated before lexical
cleanup; each scope cleans its remaining owners on each detached edge. A break
preserves an enclosing parent's remaining fields, whereas leaving the parent's
scope drops them. Sampled ordinary and labelled continues restore the next
iteration's retained frame. No new incorrect acceptance was confirmed; the
accounting implementation is unchanged.

| Case | Passing / failing bound (bytes) | Independent peak calculation |
| --- | --- | --- |
| Field returned from one branch | 121 / 120 | Flag 1 + parent slot 16 + both payloads 96 + result handle 8 |
| Field moved before an early-return branch | 249 / 248 | Same 121 + scratch 128 on the continuing path |
| Return from stored / temporary Option match | 120 / 119; 137 / 136 | Parent binding 16 + payloads 96 + result handle 8; temporary input adds 17 |
| Return through a nested loop | 137 / 136 | Branch case 121 + nested box 16 |
| Return from boxed parent | 129 / 128 | Branch case 121 + outer box handle 8 |
| Return from matched field of an enclosing owner | 161 / 160 | Enclosing slot 25 + tag payload 16 + pair payloads 96 + binding 16 + result handle 8 |
| Break preserves an enclosing parent | 248 / 247 | Remaining parent/sibling 48 + detached child 72 + later scratch 128 |
| Labelled break leaves parent and nested scopes | 136 / 135 | Pair slot 16 + both payloads 96 + nested box 16 + result handle 8 |
| Ordinary / labelled continue after a partial move | 145 / 144; 161 / 160 | Retained box/counter 25 + pair slot 16 + both payloads 96 + moved handle 8; nested box adds 16 |
| Caller retains a returned field | 265 / 264 | Flag 1 + returned child 72 + scratch 192 |
| Incoming field exit / retained caller result | 121 / 120; 264 / 263 | Helper parameters 17 + result handle 8 + incoming payloads 96; or returned child 72 + scratch 192 |
| Partial return from a memory section | 120 / 119 | Parent slot/payloads 112 + section result handle 8 |

Stored matches construct the Option payload directly in its destination. A
temporary match additionally keeps its 17-byte input alive through the arm.
Separate return sites may each report the one-byte-short failure; tests require
every diagnostic to be a budget violation. All six focused tests pass.

Validation against the rebuilt verifier: all 919 memory integration tests and 44
resource examples passed without retries. Memory unit tests passed 41 tests with
one existing manual measurement ignored. Formatting for `vir` and
`rust_verify_test`, Clippy for `rust_verify_test --test resource`, whitespace
checks, and all eleven tracker links passed. This pass changes only tests and
this tracker; the accounting and runtime-query implementations are unchanged.

Remaining coverage: deeper runtime-collection results and broader combinations
of conditional replacements, input provenance, and multiple exits remain open.
These samples do not establish exhaustive exit coverage or resolve the earlier
solver-limit sensitivity. Runtime-query evaluation was not revisited. Unrelated
documentation moves remain outside this pass.

## Proof-obligation placement and erasure

- [x] Inspect obligation creation in `analysis.rs`, checkpoint and section checks,
  and `symbolic.rs` site attachment. Follow `memory::check_crate` through frontend
  `pipeline.rs` and `query.rs` to annotation erasure and ordinary `ast_to_sst.rs`
  assertion lowering. Inspect budget specialization in `contracts.rs` and
  proof-state scheduling in `growth.rs` and `vectors.rs`.
- [x] Add direct VIR tests in
  [`symbolic.rs`](../../../source/vir/src/resource/memory/symbolic.rs): an unmatched
  required site is rejected, and erasure removes a checkpoint marker while
  preserving a failing generated inequality as an assertion, without replacing
  it with an assumption.
- [x] Add 12 independently calculated passing/one-byte-short pairs and two
  additional controls in
  [`proof_obligations.rs`](../../../source/rust_verify_test/tests/resource/memory/proof_obligations.rs).
- [x] Finish broad validation and commit this bounded pass.

The frontend invokes the memory pass on mode-checked, unsimplified local bodies.
It instruments checks before erasing annotations. Generated inequalities use
`AssertAssume { is_assume: false }`; ordinary assertion lowering retains a proof
obligation. The instrumenter rejects unmatched required inequality sites and
attaches entry, declaration, and expression checks at their respective sites.
No incorrect acceptance was confirmed in these samples; implementation behavior
is unchanged, with additions confined to tests and this tracker.

| Cases | Passing / failing bound (bytes) | Independent peak calculation |
| --- | --- | --- |
| Function entry | 8 / 7 | One u64 input |
| Initialized slot, uninitialized slot, standalone aggregate, and returned aggregate | 72 / 71 each | Input 8 + array 64 |
| Unit-valued helper call | 72 / 71 | Caller input 8 + callee allowance 64 |
| Later call argument | 88 / 87 | Caller input 8 + pending first argument 16 + later scratch 64 |
| Active branch and suffix after an early return | 73 / 72 each | Inputs 9 + scratch 64 |
| Skipped branch and early-return suffix | 9 / 8 each | Inputs 9; scratch is unreachable |
| Repeated loop body | 74 / 73 | Inputs/counter 10 + per-iteration scratch 64 |

Each contract uses an immutable runtime `limit` parameter, fixed only by a
precondition. Short-bound tests require budget diagnostics at the charged source
site. Positive skipped-path controls reject unconditional hoisting of unreachable
charges. A zero-visit loop fits 10 bytes despite a syntactic 64-byte body
allocation; another control checks that valid current/peak checkpoints do not
prove `assert(false)`. All five focused integration tests and three symbolic
unit tests pass, including the existing memory-kind selection test.

Validation against the rebuilt verifier: all 924 memory integration tests and 44
resource examples passed without retries. Memory unit tests passed 43 tests with
one existing manual measurement ignored. Formatting for `vir` and
`rust_verify_test`, Clippy for `vir --lib --tests` and
`rust_verify_test --test resource`, whitespace checks, and all 25 tracker links
passed. Changes are limited to tests and this tracker; no public API, accounting
rule, or runtime-query implementation changed.

Remaining audit: snapshot/update ordering and complete attachment of scheduled
proof-state actions, generated loop invariant entry/back-edge/exit proofs,
verification selection and bypass flags, and metadata/summary agreement. The
instrumenter's unmatched-site guard covers required inequalities and capacity
checks; the `growth.before`, `updates`, `after`, and loop maps need a separate
coverage audit. No dropped supported proof-state action was reproduced here.
The broad core checklist remains open. Runtime-query evaluation and the earlier
solver-limit sensitivity were not revisited. Unrelated documentation moves remain
outside this pass.
