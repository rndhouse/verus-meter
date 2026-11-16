# 3. Additional expressions and spec helpers

## Goal

Expand the working query path to useful existing resource formulas, adding
focused tests as each expression kind is supported.

## Work

- [x] Reuse the resource AST, model-size resolution, and argument substitution.
  Keep memory-specific adaptation under `resource/memory/` and shared extraction
  under `resource/runtime/` where appropriate.
- [x] Add multiple supported unsigned scalar inputs, Boolean inputs, comparisons,
  Boolean operators, and conditionals. Preserve parameter order and Rust types.
- [x] Resolve `value_size` and `ref_size` using existing model layouts. Keep these
  source-model quantities distinct from Rust ABI `size_of`.
- [x] Support simple local, nongeneric numeric spec helpers with bodies reducible
  to the supported operations, including local bindings, nested helper calls,
  supported casts to mathematical integers, and conditional branches.
- [x] Inspect all reachable helper expressions. Diagnose recursive dependencies,
  functions returning functions, unsupported casts or operations, external bodies,
  and unavailable definitions with useful source locations.
- [x] Derive retained data from the original formula and helper definitions. Test
  that changing either reaches the compiled query without a second user-maintained
  formula or stale artifact.
- [x] Assess `peak(helper(args))` through existing contract resolution. Include it
  if existing substitution makes it straightforward; otherwise provide an explicit
  diagnostic and record it as a follow-up. Preserve current argument-free
  `peak(helper)` semantics.
- [x] Test direct and helper-based formulas against concrete expected answers,
  parameter substitution, selected branches, and unsupported nested expressions.
  Ensure unannotated contracts retain their existing supported scope.

## Acceptance

Each supported operation works in a compiled query and has focused test coverage.
Simple spec helpers work without an executable copy supplied by the user.
Unsupported queried expressions fail clearly during compilation. No formal
equivalence proofs are required.

## Starting points

- [Budget representation and resolution](../../../../../source/vir/src/resource/memory/budget.rs)
- [Contract lowering and substitution](../../../../../source/vir/src/resource/memory/contracts.rs)
- [Spec-helper admission](../../../../../source/vir/src/resource/memory/spec_budget.rs)
- [Frontend resource lowering](../../../../../source/rust_verify/src/resource/memory/)
- [Simple helper example](../../../../../examples/resource/memory/contracts/spec_budgets.rs)
- [Higher-order example, deferred for queries](../../../../../examples/resource/memory/contracts/function_budgets.rs)

Accounting validates spec calls and leaves their bodies to ordinary Verus
reasoning. Runtime extraction separately inspects supported bodies before ghost
erasure.

## Implemented boundary

Implemented on `feature/queryable-peak-memory` in commit `f21c21d4d`. Queries
retain multiple unsigned and Boolean inputs, comparisons and logical operators,
conditionals, immutable local bindings with shadowing, nested spec-helper calls,
and nonnegative casts to mathematical integers. Both spec calls and
`peak(helper(arguments))` use the same capture-free argument substitution.
Changing a helper body updates compiled queries and dependent peak allowances.

Helper and peak targets must be named directly in the same `verus!` item scope.
Recursion, higher-order application, unavailable or external helpers, native
casts, unsupported arithmetic, and argument-free `peak(helper)` are diagnosed.
All reachable initializers and branches are inspected. Existing unannotated
resource contracts retain their supported expressions and peak semantics.

Model-size constants use Rust type resolution, including aliases, and hidden
runtime size traits. The small `source/verus-meter/model/` crate shares primitive
width, array arithmetic, and reference-width policy with the verifier's layouts.
The supported runtime size subset covers primitive values, fixed integer arrays,
standard owning handles, and references to sized values or slices. Custom struct
sizes remain unsupported and produce trait diagnostics; computed helper locals
may need explicit source type annotations for size queries. No ABI `size_of`
substitution is used. Source-level correctness and resource obligations remain
with Verus; runtime extraction and interpretation remain tested tooling.
