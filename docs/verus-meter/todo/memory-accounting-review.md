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

## Open-findings fix queue

Fix and validate each recorded open issue in its own commit. The earlier three
source/runtime findings and the proof-state attachment gap are already fixed.
The broad core checklist above remains review coverage, not a list of confirmed
bugs.

- [x] Restore the tight append-only scalar vector bound after a loop.
- [x] Preserve checked metadata on partial loop exits for later allocations.
- [x] Admit scalar-only argument loops without disabling allocation-effect guards.
- [x] Reproduce and address the recorded delegated-extraction solver-limit
  sensitivity without raising the default limit or weakening failure checks.

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

## Proof-state scheduling

- [x] Inspect `symbolic.rs` attachment of `growth.before`, `updates`, `after`,
  loop invariants, loop ensures, and single-visit/exit annotations. Follow snapshot
  substitution in `growth.rs`, vector growth commits in `vectors.rs`, and
  `EvalAndResolve` execution order in `ast_to_sst.rs`.
- [x] Check discarded extraction against frontend temporary wrappers. The
  frontend gives wrappers fresh VIR identities; the survivor-bound source probe
  passes before the fix. No duplicate source transition was reproduced.
- [x] Reproduce silently omitted proof-state schedules through the instrumenter
  interface, reject unmatched or ambiguous execution sites, and check action
  ordering directly. Require loop annotations to match actual loop expressions;
  permit entry snapshots without treating entry sites as operation commits.
- [x] Add eight independently calculated passing/one-byte-short pairs in
  [`proof_state.rs`](../../../source/rust_verify_test/tests/resource/memory/proof_state.rs).
- [x] Finish broad validation and commit this bounded pass.

Previously, an unmatched required budget inequality was rejected, but an
unmatched scheduled metadata action or loop annotation was silently ignored.
A direct VIR test failed against that implementation: a `growth.before` action
with no matching expression was accepted. Such a lowering mismatch could leave
initialized proof counters in place of required transitions. No accepted
Rust-source byte-bound violation was demonstrated through this interface issue.

The instrumenter now distinguishes assertion sites, expression attachment sites,
and loop sites. Every nonempty snapshot/transition/commit schedule must attach to
its supported site; loop maps and flags must attach to loops. Repeated action
sites and collisions between entry snapshots and expression sites are rejected.
The unit tests cover every schedule class, wrong-kind loop sites, entry-only
sites, duplicate execution sites, and the order snapshot, budget assertion,
transition, source operation, commit. `EvalAndResolve` executes the commit only
after a normally completing operation and preserves its result.

| Cases | Passing / failing bound (bytes) | Independent peak calculation |
| --- | --- | --- |
| Discarded vector removal | 360 / 359 | Handle 24 + unchanged backing 16 + surviving payload 64 + scratch 256 |
| Growth replacement overlap | 44 / 43 | Handle 24 + old buffer 4 + new buffer 16 |
| Committed growth and later scratch | 168 / 167 | Handle 24 + retained backing 16 + scratch 128 |
| Conditional growth / two loop iterations | 169 / 168 each | Same 168 + flag or counter 1; the loop recreates and releases its vector and scratch each visit |
| Growth through a struct field | 192 / 191 | Struct slot 32 + backing 16 + tag payload 16 + scratch 128 |
| Helper replacement summary | 176 / 175 | Handle 24 + retained declared helper allowance 24 + scratch 128 |
| Growth inside a memory section | 168 / 167 | Section handle 24 + retained backing 16 + scratch 128 |

Validation against the rebuilt verifier: all 928 memory integration tests and 44
resource examples passed without retries. Memory unit tests passed 48 tests with
one existing manual measurement ignored. Formatting for `vir` and
`rust_verify_test`, Clippy for `vir --lib --tests` and
`rust_verify_test --test resource`, whitespace checks, and all 26 tracker links
passed. Five new unit tests cover the instrumentation boundary; four new
integration tests exercise the eight bound pairs. The memory-model rules and
runtime-query implementation are unchanged.

Precision follow-up: preliminary loops growing an enclosing `Vec<u32>` rejected
`current(memory) <= 41`, although the concrete retained buffer is 16 bytes.
Scalar-element vectors do not use the length-linked invariant enabled for owning
elements; their loop summary bounds backing in terms of capacity metadata.
This rejection does not demonstrate undercounting. Exact post-loop capacity
precision remains outside this pass; the regression repeats a local allocation
to check transition execution on every visit with a precise bound.

Remaining audit: generated loop invariant entry/back-edge/exit proofs,
verification selection and bypass flags, and metadata/summary agreement. These
attachment checks do not establish the semantic correctness of every scheduled
action or invariant. Runtime-query evaluation and the earlier solver-limit
sensitivity were not revisited. Unrelated documentation moves remain outside
this pass.

## Loop proof entry, back edges, and exits

- [x] Inspect `loops/analysis.rs`, `analysis/charges.rs`, `evidence.rs`,
  `visits.rs`, and `nested.rs`: generated charge/progress/headroom facts remain
  proof candidates, and nested entries snapshot the current parent visit.
- [x] Follow `metadata.rs` snapshot freezing and `symbolic.rs` invariant kinds
  into the ordinary `ast_to_sst.rs` / `sst_to_air.rs` entry, body-end, continue,
  and break proof obligations. Inspect `control.rs` and `lifetime.rs` restoration
  of reachable continue edges before no-back-edge classification.
- [x] Add ten independently calculated passing/one-byte-short pairs and ten
  additional logical controls in
  [`loop_proofs.rs`](../../../source/rust_verify_test/tests/resource/memory/loop_proofs.rs).
- [x] Finish broad validation and commit this bounded pass.

Regular generated resource invariants are checked before the loop and on normal
back edges and continues. In isolated loops, their exit facts must also be proved
at breaks before being assumed outside. Partial breaks, returns, and exits to
enclosing labels select `InvariantExceptBreak` for resource facts, so completed
visit relationships are not assumed on those exits. Head breaks that close the
iteration count have a separately checked completed-count postcondition.

The visit ordinal increments after a normally completed body, or before a
continue; `EvalAndResolve` skips the body-end increment when control has already
exited. Continue states restore reachability before the no-back-edge decision.
Loops with no fallthrough or local continue use ordinary verification without
loop isolation and retain their real entry/exit state. That path does not assume
header invariants after a break: the control that increments `i` from zero and
breaks still rejects a subsequent `assert(i == 0)`.

| Cases | Passing / failing bound (bytes) | Independent peak calculation |
| --- | --- | --- |
| Late allocation after normal, unconditional-continue, or conditional-continue back edges | 633 / 632 each | Retained root 72 + vector handle 24 + backing 17*8 + counter 1 + 17 payloads of 16 + scratch 128 |
| Allocation immediately before a partial break or return | 633 / 632 each | Same retained storage; the final payload exists before the counter advances |
| Nested loop on outer visit 17 | 634 / 633 | Same 633 plus the live inner u8 counter |
| Unconditional loop with a closing head break | 633 / 632 | Same retained storage and late allocation as the normal back-edge case |
| Caller retains the completed loop's returned collection | 2552 / 2551 | Caller root 72 + returned vector 24 + backing 136 + payloads 272 + scratch 2048; the 1024-byte helper allowance also fits at the call |
| Taken / skipped single visit | 249 / 248; 233 / 232 | Boolean input 1 + root 72 + vector handle/backing 32 + scratch 128; taken visit adds one retained 16-byte payload |

The first peak probes require an allocation on visit 17, beyond the finite
summary window. Six logical controls reject reachable `assert(false)` statements
at entry, on a later visit, before continue/return, after a partial break, and
after full completion. Three invalid user-invariant controls fail at entry, body
end, and continue; a fourth checks the actual single-visit exit state. Multiple
invariant diagnostics are permitted, but every diagnostic must have the expected
proof-failure class. No incorrect accepted byte bound or inconsistent generated
fact was confirmed in these samples. Implementation behavior is unchanged.

Validation against the rebuilt verifier: all 935 memory integration tests and 44
resource examples passed on their full runs without retries. All seven focused
tests passed. Memory unit tests passed 48 tests with one existing manual
measurement ignored. Formatting for `vir` and `rust_verify_test`, Clippy for
`rust_verify_test --test resource`, whitespace checks, and all 27 tracker links
passed. Changes are confined to regression tests and this tracker.

Precision follow-up: a partial break after the final push rejects a subsequent
128-byte scratch allocation under the concrete 633-byte peak, even with user
invariants bounding the final length. Generated resource facts are not exported
on that partial exit, leaving insufficient metadata for the post-loop check.
Putting scratch before the break verifies at 633 and rejects 632. This is a
rejection of a fitting program, not a demonstrated undercount; improving partial
exit metadata requires a separate design and proof pass.

Remaining audit: broader labelled exits, nested partial exits, and the semantic
validity of each metadata lemma and inferred ownership summary. The sampled
entry/back-edge/exit checks do not close the broad loop-composition or proof
integration checklist items. Verification selection and bypass behavior are the
next bounded pass, followed by metadata/summary agreement. Runtime-query
evaluation and the earlier solver-limit sensitivity were not revisited.
Unrelated documentation moves remain outside this pass.

## Append-only loop buffer fix

The empty and initially one-element scalar-vector probes reproduced rejection of
`current(memory) <= 41` after two pushes in a loop. The concrete final storage is
a 24-byte handle, a 16-byte buffer, and a one-byte counter; adding a 128-byte
scratch array gives a 169-byte peak.

`vectors.rs` now records append-only length observations for scalar elements as
well as owning elements. The checked backing invariant in `growth.rs` uses the
largest possible pre-append length, `current_length - 1`, for the most recent
replacement, rather than allowing another replacement at the current length.
Initial backing and helper-retention floors remain charged. Pop/remove still
invalidate the append-only observation, so emptying a grown vector cannot
restore its original smaller allocation in the accounting.

Both probes now pass at 169 and reject 168. A separate removal regression keeps
the grown buffer after two pops and rejects an allowance that counts only its
original four-byte backing. All 19 focused growth tests pass. These changes
resolve the scalar-vector precision case recorded above; they do not promise
exact capacity inference for every supported loop.

Validation: rebuilt verifier; 48 memory unit tests passed (one existing manual
measurement ignored), all 19 focused growth tests and 44 resource examples
passed. The full memory run passed 936 tests and failed one existing fixed-role
extraction negative case on a solver resource-limit diagnostic; that complete
test passed unchanged at the default limit on focused retry. Its concrete input
is now retained as `fixed_role_extraction_short` in
`loop_ownership::disjoint_fixed_roles_transfer_nested_children_with_a_symbolic_count`.
This evidence keeps the solver-robustness queue item open. Formatting, Clippy for
`vir --lib --tests` and the resource test target, whitespace checks, and tracker
references passed. No limit was raised and no failure assertion was relaxed.

## Partial-loop exit metadata fix

The retained-allocation probe reproduced rejection of a post-break current-memory
check. `loops/analysis.rs` now emits separate checked exit predicates for current
vector backing, element metadata, element charge bounds, and unchanged backing
frames. Verus must prove these predicates at every break and normal completion.
Progress, conservation, and frozen head observations remain head-only; they are
not promoted to exit assumptions for a partial visit.

The new regression retains 1, 7, or 17 payloads after a partial break, then
allocates scratch outside the loop. Passing/one-byte-short peaks are 377/376,
473/472, and 633/632 bytes: root 72 + vector handle/backing 160 + counter 1 +
payloads of 16 + scratch 128. A Boolean-controlled early break also permits full
normal completion and passes at 634, rejecting 633. All eight focused loop-proof
tests pass, including the existing reachable-assertion and invalid-invariant
controls. The confirmed fitting-program rejection is resolved without assuming
completed-visit facts on the partial exit.

Validation: rebuilt verifier; all 938 memory integration tests and 44 resource
examples passed on their full runs without retries. Memory unit tests passed
48 tests with one existing manual measurement ignored. Formatting for `vir` and
`rust_verify_test`, Clippy for `vir --lib --tests` and the resource test target,
whitespace checks, and tracker references passed. The intermittent solver-limit
case passed in this run; its robustness fix remains separately queued.

## Argument-loop proof bookkeeping fix

The original inline scalar-loop reproduction failed before call composition,
despite a generous allowance. The allocation-effect revision counted erased
loop snapshots, visit ordinals, and read-only metadata proofs as if they changed
collection allocation state. Retained collections exposed the same issue through
their metadata activation and shape proofs.

`growth.rs` now distinguishes explicitly registered loop proof locals and
read-only loop proof actions from allocation-state actions. Proof statements
keep their existing order and are still verified. Writes to allocation counters
and unclassified actions continue to invalidate argument composition; the guard
is not disabled. Local control-flow exits inside arguments retain their prior
support restriction.

Seven passing/one-byte-short pairs in `argument_ownership.rs` cover normal,
conditional, and nested loops while an earlier owner is pending, plus returned
ownership and a retained collection used by a later helper. Pending root/owner/
workspace peaks are 241/240, or 242/241 with both nested counters live; returned
ownership overlaps later scratch at 304/303; retained collection storage gives
265/264. A generous-bound negative control still rejects actual vector growth
inside an argument. All 11 focused argument-ownership tests pass. Branches may
report multiple short-bound errors, and every diagnostic must be a budget
failure; solver-limit and unrelated errors remain test failures.

Validation: rebuilt verifier; 48 memory unit tests passed (one existing manual
measurement ignored), all 11 focused argument-ownership tests and 44 resource
examples passed. The full memory run passed 939 tests; the existing ordered-
append test reported its intended short-bound failure plus a loop-query resource
limit. That entire test passed unchanged at the default limit on focused retry.
The concrete remaining reproduction is `direct_block_short` in
`loop_ownership::ordered_append_blocks_compose_direct_helpers_and_nested_loops`.
Formatting, Clippy for `vir --lib --tests` and the resource target, whitespace,
and tracker references passed. The solver failure remains queued separately.

## Stable symbolic accounting order

Two fresh verifier processes for `direct_block_short` emitted different
parenthesized symbolic sums from the same source. `Live::dynamic` used hash
iteration when constructing the charged-byte expression, changing SMT term order
and metadata quantifier behavior. The observed ordered-append and fixed-role
extraction limit failures therefore had a concrete nondeterministic input to the
solver, even though the mathematical totals agreed.

`accounting.rs` now orders dynamic charges by allocation identity. A regression
compares formulas across eight insertion orders and checks that all eight
allocations remain present. It fails with the old hash map and passes with the
ordered map. Two fresh profiled runs of the recorded ordered-append input now
produce byte-identical AIR and identical solver resource counts. The ordering
fix changes no byte rule, proof assertion, or solver limit.

A default-limit regression in `loop_ownership.rs` covers direct and delegated
loop extraction in three fresh-process passing/short-bound pairs each. The
4180-byte peak is selected handle 24 + backing 48 + transferred payloads 4+8 +
scratch 4096; 4179 must report only the budget violation. Both the 512-byte direct
helper allowance and the delegated 600-byte allowance fit below that later
peak. All twelve checks pass without a limit override, and the existing 14-test
loop-ownership suite passes. This removes the identified formula-order
instability; it does not guarantee bounded solver work for arbitrary programs.

Validation: rebuilt verifier; all 941 memory integration tests and 44 resource
examples passed on their full runs without retries or limit overrides, including
the recorded ordered-append and fixed-role extraction cases. Memory unit tests
passed 49 tests with one existing manual measurement ignored. Formatting for
`vir` and `rust_verify_test`, Clippy for `vir --lib --tests` and the resource test
target, whitespace checks, and all 27 tracker references passed. All four entries
in the fix queue are addressed; the broader core guarantee audits remain open.
