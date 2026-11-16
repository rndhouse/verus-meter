# Critical memory review

Review the soundness boundaries of the [memory model](../model.md): an accepted
contract must bound all simultaneous storage charged by that model. This is a
focused review of critical paths, not an exhaustive audit of the fork.

## Progress

- [x] Heap ownership and peak accounting: moves, drops, nested allocations,
  replacement overlap, branch joins, and lexical exits.
- [x] Function and loop composition: retained caller allocations, declared slack,
  returned ownership, accumulating iterations, branches, and early exits.
- [x] Trust boundaries: unsupported operations, verification instrumentation,
  bypasses, and agreement between runtime queries and verified contracts.
- [x] Validate the two fixes and commit the completed work.

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
They support the sampled checks above, not an exhaustive audit.

## Findings and fixes

### P1: skipped short-circuit operands released live storage

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

### P1: custom size-trait implementations falsified runtime allowances

Before the fix, a safe downstream `ValueSize` implementation returning zero made
a generated query report zero for `value_size(Buffer)`, while Verus checked the
same contract as 64 bytes. No unsafe code or verification bypass was necessary.

[`layout.rs`](../../../source/verus-meter/runtime/src/layout.rs) now seals
`ValueSize` and `ReferenceSize`, preserving the existing supported types while
preventing downstream byte-count implementations. Compile-fail doctests cover
both traits; the original generated-query reproduction is covered by
[`regressions.rs`](../../../source/verus-meter/runtime/tests/query/regressions.rs).
Validated by eight runtime unit tests, three doctests, and all 12 compiled query
tests, including runtime bundle refresh, relocation, and a Cargo client.

### P1: wildcard patterns released ignored owners

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
