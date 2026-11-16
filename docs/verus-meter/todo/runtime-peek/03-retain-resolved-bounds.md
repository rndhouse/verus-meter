# 3. Retain resolved bounds

## Goal

Derive executable expression data from the same contract used by resource
verification, preserving its mathematical interpretation and parameter bindings.

## Work

- [ ] Reuse the existing resource AST, size resolution, and argument substitution.
  Put memory-specific adaptation under `resource/memory/` and shared expression
  extraction under `resource/runtime/` where appropriate.
- [ ] Lower constants, scalar inputs, sums, products, supported predicates and
  branches into the runtime representation. Keep source spans for diagnostics.
- [ ] Resolve `value_size` and `ref_size` using existing model layouts. Do not
  substitute Rust ABI `size_of` for the source-level storage model.
- [ ] Follow simple local, nongeneric numeric spec helpers with verified bodies.
  Support their local bindings, nested supported helper calls, mathematical casts,
  and conditionals. Validate the entire reachable body, not just the return type.
- [ ] Preserve one authoritative formula: helper expansion or expression sharing
  must be a checked derivation, with no manually maintained executable formula.
- [ ] Diagnose recursive helper dependencies, higher-order spec applications,
  unsupported casts or operations, external bodies, and unavailable definitions.
  Do not reduce the scope of non-queryable contracts that already accept them.
- [ ] Assess `peak(helper(args))` through existing contract resolution. Include it
  if the same checked substitution path suffices; otherwise leave a precise
  first-version diagnostic and documented follow-up. Preserve current semantics
  of argument-free `peak(helper)` rather than inventing maximization behavior.
- [ ] Validate that expression data cannot refer to erased runtime inputs or
  unresolved ghost entities. Preserve model assumptions and target information
  through the compilation bridge chosen in task 1.

## Acceptance

A direct formula and a supported equivalent helper produce the same runtime
answer, with a formal connection to their respective original contracts. Changes
to the bound or a helper body update both verification and the query. Unsupported
queried bodies fail at compile time with useful locations, including when hidden
behind a helper call. No unchecked fallback replaces a failed translation.

## Starting points

- [Budget representation and resolution](../../../../source/vir/src/resource/memory/budget.rs)
- [Contract lowering and substitution](../../../../source/vir/src/resource/memory/contracts.rs)
- [Spec-helper admission](../../../../source/vir/src/resource/memory/spec_budget.rs)
- [Frontend resource lowering](../../../../source/rust_verify/src/resource/memory/)
- [Simple helper example](../../../../examples/resource/memory/contracts/spec_budgets.rs)
- [Higher-order example, deferred for queries](../../../../examples/resource/memory/contracts/function_budgets.rs)

Currently, accounting validates spec calls but leaves their bodies to ordinary
Verus reasoning. Runtime extraction of those bodies is new work, not an existing
interpreter that can simply be exposed.
