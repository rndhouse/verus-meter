# 4. Attribute and executable queries

## Goal

Finish integrating the prototype's typed query interface, including visibility,
diagnostics, and ordinary build workflows.

## Work

- [x] Review `#[queryable_peak_memory]` handling through Verus's macro machinery.
  Select the function signature's declared `peak(memory)` bound structurally; ignore
  body sections and checkpoint assertions when selecting the exported allowance.
- [x] Preserve existing resource-clause syntax. No syntax expansion for work or CPU
  cycles is part of this task; avoid an architecture that prevents selecting a
  specific quantity if multiple resource kinds are added later.
- [x] Finalize the `foo::peak_memory_bound(...)` interface or explain any
  compiler-driven adjustment before establishing a different public convention.
  Mirror supported parameter types and visibility, with hygienic bindings and
  explicit collision handling.
- [x] Emit only wrappers and expression data. Delegate evaluation to the shared
  runtime library, without per-function duplicated arithmetic or runtime Z3 calls.
- [x] Check generation uses the current retained expression across verification and
  compilation passes. Preserve the project's existing verification/compilation
  guarantees and describe any bypass modes without overstating enforcement.
- [x] Document that querying evaluates an allowance and does not automatically
  check the target function's preconditions. Specify query behavior outside those
  preconditions without generating runtime precondition checks in this version.
- [x] Reject missing contracts, duplicate attributes, unsupported signatures, and
  unsupported queried expressions with actionable diagnostics. Do not accidentally
  expose a private function's query publicly.
- [x] Integrate runtime crate discovery, linking, and artifact preparation through
  existing build facilities, preserving package publishing settings.
- [x] Test normal free-function calls alongside query calls, argument type errors,
  name collisions, nested modules, visibility, and erasure behavior through focused
  boundaries rather than a combinatorial spelling matrix.

## Acceptance

A Rust executable calls the generated interface with concrete arguments and no
ghost values. Wrong argument types fail compilation. Missing or unsupported
contracts fail during compilation rather than leaving an unusable runtime query.
The function itself remains callable normally, and changing its signature updates
the generated interface. A clean rebuild does not rely on stale expression data.

## Starting points

- [Resource macro modules](../../../../../source/builtin_macros/src/resource/)
- [Syntax integration](../../../../../source/builtin_macros/src/syntax.rs)
- [Frontend attribute handling](../../../../../source/rust_verify/src/attributes.rs)
- [Verifier and compilation integration](../../../../../source/rust_verify/src/)
- [Build tasks](../../../../../source/Makefile.toml)

## Implemented boundary

Implemented on `feature/queryable-peak-memory` in commit `70463f9c3`. The
`foo::peak_memory_bound(...)` namespace follows the source function's visibility,
argument types and order, configuration, and test-only removal. Diagnostics cover
duplicate attributes, unsupported signatures or placement, and occupied namespaces.
Raw identifiers and generated expression bindings preserve source arguments.
Selection uses the signature contract, independently of body sections and checkpoints.

Place the query attribute directly on the function. Conditional query markers and
configuration-controlled helper or peak targets are rejected explicitly. Queries
evaluate the declared allowance for supplied inputs without checking execution
preconditions; verification bypass modes retain their existing behavior.

A Rust preparation tool builds an isolated runtime bundle from Cargo artifacts.
Standalone Verus discovers it automatically, and release staging carries its
dependency closure. Default build workflows invoke preparation. Cargo clients
declare the runtime dependency explicitly and use Cargo's resolved libraries.
Compiled tests cover both paths, relocated distributions, bundle refresh, and
rebuilding after a formula or signature changes.
