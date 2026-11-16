# 3. Additional expressions and spec helpers

## Goal

Expand the working query path to useful existing resource formulas, adding
focused tests as each expression kind is supported.

## Work

- [ ] Reuse the resource AST, model-size resolution, and argument substitution.
  Keep memory-specific adaptation under `resource/memory/` and shared extraction
  under `resource/runtime/` where appropriate.
- [ ] Add multiple supported unsigned scalar inputs, Boolean inputs, comparisons,
  Boolean operators, and conditionals. Preserve parameter order and Rust types.
- [ ] Resolve `value_size` and `ref_size` using existing model layouts. Keep these
  source-model quantities distinct from Rust ABI `size_of`.
- [ ] Support simple local, nongeneric numeric spec helpers with bodies reducible
  to the supported operations, including local bindings, nested helper calls,
  supported casts to mathematical integers, and conditional branches.
- [ ] Inspect all reachable helper expressions. Diagnose recursive dependencies,
  functions returning functions, unsupported casts or operations, external bodies,
  and unavailable definitions with useful source locations.
- [ ] Derive retained data from the original formula and helper definitions. Test
  that changing either reaches the compiled query without a second user-maintained
  formula or stale artifact.
- [ ] Assess `peak(helper(args))` through existing contract resolution. Include it
  if existing substitution makes it straightforward; otherwise provide an explicit
  diagnostic and record it as a follow-up. Preserve current argument-free
  `peak(helper)` semantics.
- [ ] Test direct and helper-based formulas against concrete expected answers,
  parameter substitution, selected branches, and unsupported nested expressions.
  Ensure unannotated contracts retain their existing supported scope.

## Acceptance

Each supported operation works in a compiled query and has focused test coverage.
Simple spec helpers work without an executable copy supplied by the user.
Unsupported queried expressions fail clearly during compilation. No formal
equivalence proofs are required.

## Starting points

- [Budget representation and resolution](../../../../source/vir/src/resource/memory/budget.rs)
- [Contract lowering and substitution](../../../../source/vir/src/resource/memory/contracts.rs)
- [Spec-helper admission](../../../../source/vir/src/resource/memory/spec_budget.rs)
- [Frontend resource lowering](../../../../source/rust_verify/src/resource/memory/)
- [Simple helper example](../../../../examples/resource/memory/contracts/spec_budgets.rs)
- [Higher-order example, deferred for queries](../../../../examples/resource/memory/contracts/function_budgets.rs)

Accounting currently validates spec calls and leaves their bodies to ordinary
Verus reasoning. Extracting those bodies for runtime evaluation is new work.
