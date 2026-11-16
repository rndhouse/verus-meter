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

Both findings are resolved. No additional confirmed findings in the reviewed
call/loop composition paths.
Detailed reproduction and validation evidence belongs in the fix commits.
Existing unrelated documentation moves are outside this review.

## Validation

Checks passed against the rebuilt verifier and refreshed runtime bundle:

- Memory unit tests: 41 passed; one manual proof-generation measurement ignored.
- Memory integration tests: 898 passed, including both new regression tests.
- Resource examples: 44 passed.
- Runtime: eight unit tests, three doctests, and 12 compiled query tests passed.
- Formatting for `vir`, `rust_verify_test`, and `verus_meter_runtime` passed.
- Clippy for `vir --lib`, `rust_verify_test --test resource`, and
  `verus_meter_runtime --all-targets` passed.
- Runtime rustdoc with `RUSTDOCFLAGS='-D warnings'`, whitespace checks, and review
  document references passed.
