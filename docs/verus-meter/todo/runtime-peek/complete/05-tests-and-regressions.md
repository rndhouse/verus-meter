# 5. Correctness tests and regressions

## Goal

Close meaningful test gaps across extraction, runtime evaluation, and compiled
queries. Build on tests added with each feature rather than postponing testing
until this task.

## Work

- [x] Review coverage of input conversion, argument mapping, model sizes, helper
  substitution, arithmetic, and selected branches. Add tests for distinct missing
  behavior, using independently calculated expected results.
- [x] Cover zero inputs, budget equality, values and intermediate calculations
  exceeding native integer ranges, and explicit native-conversion failures.
- [x] Exercise source and helper changes reaching compiled output, so stale or
  independently maintained formulas cannot pass integration tests unnoticed.
- [x] Cover missing contracts, unsupported nested helpers, signature restrictions,
  and wrong query argument types with focused diagnostic checks.
- [x] Retain a negative case where the original function exceeds its declared
  allowance. Query generation must not mask ordinary resource verification errors.
- [x] Test documented query behavior outside the function's preconditions. Keep
  callers responsible for establishing execution preconditions.
- [x] Run affected unannotated memory tests and upstream macro/erasure regressions
  according to the project instructions. Test actual boundaries rather than every
  syntactic variation or implementation detail.

## Acceptance

Focused tests cover the supported runtime-query behavior and compilation
boundaries. Existing resource verification still accepts and rejects the expected
programs. The extractor, evaluator, generated wrapper, and arithmetic library
require no new formal proofs; describe their correctness evidence as testing.

## Starting points

- [Resource tests](../../../../../source/rust_verify_test/tests/resource/)
- [Example test harness](../../../../../source/rust_verify_test/tests/examples.rs)
- [Memory semantics](../../../model.md)
- [Required project checks](../../../../../AGENTS.md)

## Implemented boundary

Implemented on `feature/queryable-peak-memory` in commit `00007255d`.

Compiled regressions cover every supported scalar input type, argument positions,
zero inputs, budget equality, and explicit conversion failure for results above
`u64`. A helper with a large intermediate product and a small final result checks
that evaluation preserves mathematical arithmetic throughout the calculation.
Independent expected values cover helper argument reordering, repeated arguments,
shadowing, typed local size queries, and rebuilding after a nested helper changes.

Queries outside execution preconditions can return a well-typed allowance, even
zero. A corresponding call from verified code still fails its precondition check.
A function that exceeds its resource allowance is rejected with or without the
query attribute. Unsupported nested helper bodies and peak targets without
contracts fail compilation; earlier interface tests retain signature and argument
type diagnostics.

These regressions exposed a compiler crash for a size query on a ghost local.
Size-query operands supply types rather than evaluated values; erasure now removes
their calls completely instead of revisiting ghost-local references during basic
checks. Both queried and unannotated compiled functions cover the fix. Correctness
evidence remains ordinary tests, alongside the target function's existing Verus
checks; no new formal proofs are required.
