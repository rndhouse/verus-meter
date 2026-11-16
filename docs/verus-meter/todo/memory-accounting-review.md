# Memory accounting correctness review

This tracker covers development correctness review of our own unreleased,
experimental Verus fork. Describe findings by their incorrect behavior, affected
cases, and development impact, without severity ratings.

Review the [memory model](../model.md): an accepted contract must bound all
simultaneous storage charged by that model. Focus on fork-specific memory
accounting; the completed checks do not establish exhaustive correctness.

## Progress

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
