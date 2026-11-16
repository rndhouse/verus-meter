# 5. Correctness tests and regressions

## Goal

Close meaningful test gaps across extraction, runtime evaluation, and compiled
queries. Build on tests added with each feature rather than postponing testing
until this task.

## Work

- [ ] Review coverage of input conversion, argument mapping, model sizes, helper
  substitution, arithmetic, and selected branches. Add tests for distinct missing
  behavior, using independently calculated expected results.
- [ ] Cover zero inputs, budget equality, values and intermediate calculations
  exceeding native integer ranges, and explicit native-conversion failures.
- [ ] Exercise source and helper changes reaching compiled output, so stale or
  independently maintained formulas cannot pass integration tests unnoticed.
- [ ] Cover missing contracts, unsupported nested helpers, signature restrictions,
  and wrong query argument types with focused diagnostic checks.
- [ ] Retain a negative case where the original function exceeds its declared
  allowance. Query generation must not mask ordinary resource verification errors.
- [ ] Test documented query behavior outside the function's preconditions. Keep
  callers responsible for establishing execution preconditions.
- [ ] Run affected unannotated memory tests and upstream macro/erasure regressions
  according to the project instructions. Test actual boundaries rather than every
  syntactic variation or implementation detail.

## Acceptance

Focused tests cover the supported runtime-query behavior and compilation
boundaries. Existing resource verification still accepts and rejects the expected
programs. The extractor, evaluator, generated wrapper, and arithmetic library
require no new formal proofs; describe their correctness evidence as testing.

## Starting points

- [Resource tests](../../../../source/rust_verify_test/tests/resource/)
- [Example test harness](../../../../source/rust_verify_test/tests/examples.rs)
- [Memory semantics](../../model.md)
- [Required project checks](../../../../AGENTS.md)
