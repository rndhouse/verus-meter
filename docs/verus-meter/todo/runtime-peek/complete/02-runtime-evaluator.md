# 2. Runtime expressions and evaluator

## Goal

Develop the task-1 interpreter into a small shared runtime library using exact
integer arithmetic, independently of the verifier and SMT solver.

## Work

- [x] Define a typed expression representation for integer and Boolean constants,
  parameters, addition, multiplication, comparisons, Boolean operators, and
  conditionals as needed for task 3. Keep parameter binding and valid expression
  construction straightforward; keep internal representation details private.
- [x] Use the existing arbitrary-precision dependency where suitable, after checking
  its workspace configuration. Do not implement a new big-integer library or expose
  its types in the public API.
- [x] Implement and document the supported operations. Preserve casts and
  distinctions between integer domains; reject unsupported conversions rather
  than silently wrapping or clamping them.
- [x] Evaluate only the selected conditional branch and preserve Boolean
  short-circuit semantics. Account for evaluator stack depth and allocation;
  arbitrary precision removes fixed-width overflow, not resource exhaustion.
- [x] Provide the agreed model-byte result and budget comparison operations. Native
  integer conversions, if exposed, must fail explicitly when the value does not fit.
- [x] Settle a small result/error API around actual supported failure cases.
  Define behavior for negative byte results and results exceeding `u64`, without
  weakening existing resource verification. Avoid adding an evaluation-limit
  framework or public expression-ingestion API unless the implementation needs it.
- [x] Test exact conversion of supported input types, intermediates exceeding
  `u64`, selected branches, comparison boundaries, and invalid representations if
  applications can supply them. Use mathematical expected values, not a second
  copy of the evaluator as the oracle.

## Acceptance

The runtime crate builds and runs without compiler or solver libraries. Supported
arithmetic produces exact values and can compare them to native runtime budgets.
Focused Rust tests cover arithmetic and comparison behavior. The task-1 example
uses this library. No formal verification of the evaluator or numeric backend is
required.

## Starting points

- [Workspace dependencies](../../../../../source/Cargo.toml)
- [Existing spec-to-exec support](../../../../../source/builtin_macros/src/contrib/exec_spec.rs)
- [Spec-to-exec limitations](../../../../../source/docs/guide/src/exec_spec.md)

Reuse appropriate facilities, but do not replace the agreed interpreter design
with generated per-formula executable arithmetic. The existing macro does not
directly support arbitrary mathematical `nat`/`int` representations.

## Implemented boundary

Implemented on `feature/queryable-peak-memory` in commit `db98d4c17`. The runtime
uses the existing arbitrary-precision dependency behind `ModelBytes`; callers can
compare with a native budget, display an exact allowance, or explicitly request a
fallible `u64` conversion. Negative final results and absent or mistyped inputs
produce query errors. Input conversions preserve every currently supported
unsigned type exactly; unsupported source casts remain rejected.

Private integer and Boolean nodes support indexed parameters, exact comparisons,
short-circuit logic, and selected-branch evaluation. Generated-data constructors
remain available to macros without exposing backend integer types. These runtime
operations prepare task 3; the source macro still accepts the task-1 arithmetic
subset. The example uses the new result API, and its run instructions include the
runtime dependency search path. Stack use and allocation behavior are documented
without introducing an evaluation-limit framework.
