# 2. Runtime expressions and evaluator

## Goal

Provide a small shared runtime library that evaluates retained formulas with exact
integer arithmetic, independently of the verifier and SMT solver.

## Work

- [ ] Define a typed expression representation for integer and Boolean constants,
  parameters, addition, multiplication, comparisons, Boolean operators, and
  conditionals. Specify parameter binding and representation validity invariants.
- [ ] Use the existing arbitrary-precision dependency where suitable, after checking
  its workspace configuration and the selected verification strategy. Do not
  implement a new big-integer library or expose its types in the public API.
- [ ] Define mathematical semantics and the evaluator correspondence alongside the
  executable operations. Preserve casts and distinctions between integer domains;
  reject unsupported conversions rather than silently wrapping or clamping them.
- [ ] Evaluate only the selected conditional branch and preserve Boolean
  short-circuit semantics. Account for evaluator stack depth and allocation;
  arbitrary precision removes fixed-width overflow, not resource exhaustion.
- [ ] Provide the agreed model-byte result and budget comparison operations. Native
  integer conversions, if exposed, must fail explicitly when the value does not fit.
- [ ] Keep representation validation and programmer errors distinct from supported
  query results. Define how any evaluation limits are reported without claiming
  that all allocation failures are recoverable.
- [ ] Test exact conversion of supported input types, intermediates exceeding
  `u64`, selected branches, comparison boundaries, and invalid representations if
  applications can supply them. Use mathematical expected values, not a second
  copy of the evaluator as the oracle.

## Acceptance

The runtime crate builds and runs without compiler or solver libraries. Supported
arithmetic produces exact values and can compare them to native runtime budgets.
The arithmetic adapter's trust status is explicit. Core correctness obligations
are implemented with the evaluator rather than deferred entirely to final tests.

## Starting points

- [Workspace dependencies](../../../../source/Cargo.toml)
- [Existing spec-to-exec support](../../../../source/builtin_macros/src/contrib/exec_spec.rs)
- [Spec-to-exec limitations](../../../../source/docs/guide/src/exec_spec.md)

Reuse appropriate facilities, but do not replace the agreed interpreter design
with generated per-formula executable arithmetic. The existing macro does not
directly support arbitrary mathematical `nat`/`int` representations.
