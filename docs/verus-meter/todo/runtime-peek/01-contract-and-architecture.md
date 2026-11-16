# 1. Contract and compilation architecture

## Goal

Resolve the public semantics, proof boundary, and route from a checked resource
contract to executable expression data before building broad expression support.

## Work

- [ ] Inspect current changes, applicable instructions, and verification/compilation
  passes. Trace when macros expand, resource metadata is lowered, types and helper
  definitions are available, and ghost code is erased.
- [ ] Specify the initial parameter set precisely. Prefer unsigned native integer
  and Boolean parameters; diagnose other signatures explicitly. Convert numeric
  inputs exactly and preserve positional types even for unused parameters.
- [ ] Settle the generated namespace, visibility, collision diagnostics, result
  type, budget comparison API, and any explicit fallible conversion to native
  integers. Investigate `foo::peak_memory_bound(...)` alongside free function `foo`.
- [ ] Define query behavior outside `foo`'s preconditions. Distinguish evaluating
  a formula from certifying that `foo` may execute. Do not silently treat spec
  `recommends` clauses as runtime checks or executable preconditions.
- [ ] Define behavior when a mathematical result exceeds `u64`, is negative, or
  cannot be evaluated under supported semantics. Preserve the existing resource
  checker's `u64` obligations; do not weaken them to make a query compile.
- [ ] Specify the proof/trust boundary: mathematical expression semantics, runtime
  evaluator, arbitrary-precision adapter, and extraction from the source contract.
  Assess existing verification facilities before deciding whether backend
  operations need a small trusted interface. Make any unresolved trust decision
  explicit to the user before claiming a fully verified feature.
- [ ] Build a minimal development experiment taking one parameterised bound through
  verification, erasure, and compiled runtime evaluation. This is an architecture
  check, not the complete implementation or proof.
- [ ] Decide how the retained artifact is passed between stages and tied to the
  exact source, parameter mapping, and memory model. Avoid stale side files,
  absolute paths, or independent re-parsing that can diverge from verification.
- [ ] Establish runtime crate packaging under `source/verus-meter/` and focused
  `resource/runtime/` integration modules. Check how prepared build tools provide
  runtime dependencies to compiled examples without implicit tool provisioning.

## Acceptance

A compiled experiment demonstrates that the chosen bridge works. Record the
durable architecture next to its implementation and the proof boundary in concise
user-facing documentation. Subsequent tasks have a concrete public API and an
explicit equivalence claim; an unresolved compilation bridge or trust question
must not be hidden behind a successful arithmetic demonstration.

## Starting points

- [Architecture](../../../../source/CODE.md)
- [Macro integration](../../../../source/builtin_macros/src/syntax.rs)
- [Resource macros](../../../../source/builtin_macros/src/resource/)
- [Compiler driver](../../../../source/rust_verify/src/driver.rs)
- [Workspace and existing arithmetic dependency](../../../../source/Cargo.toml)
