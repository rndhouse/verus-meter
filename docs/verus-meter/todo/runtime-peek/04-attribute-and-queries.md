# 4. Attribute and executable queries

## Goal

Expose retained memory bounds through a typed Rust interface that survives ghost
erasure and works in compiled application code.

## Work

- [ ] Recognise `#[queryable_peak_memory]` through Verus's macro machinery. Select
  the function signature's declared `peak(memory)` bound structurally; ignore
  body sections and checkpoint assertions when selecting the exported allowance.
- [ ] Preserve existing resource-clause syntax. No syntax expansion for work or CPU
  cycles is part of this task; avoid an architecture that prevents selecting a
  specific quantity if multiple resource kinds are added later.
- [ ] Generate the agreed `foo::peak_memory_bound(...)` interface or explain any
  compiler-driven adjustment before establishing a different public convention.
  Mirror supported parameter types and visibility, with hygienic bindings and
  explicit collision handling.
- [ ] Emit only wrappers and expression data. Delegate evaluation to the shared
  runtime library, without per-function duplicated arithmetic or runtime Z3 calls.
- [ ] Connect generation to the checked retained artifact across verification and
  compilation passes. Preserve the project's existing verification/compilation
  guarantees and describe any bypass modes without overstating enforcement.
- [ ] Reject missing contracts, duplicate attributes, unsupported signatures, and
  unsupported queried expressions with actionable diagnostics. Do not accidentally
  expose a private function's query publicly.
- [ ] Integrate runtime crate discovery, linking, and artifact preparation through
  existing build facilities, preserving package publishing settings.
- [ ] Test normal free-function calls alongside query calls, argument type errors,
  name collisions, nested modules, visibility, and erasure behavior through focused
  boundaries rather than a combinatorial spelling matrix.

## Acceptance

A Rust executable calls the generated interface with concrete arguments and no
ghost values. Wrong argument types fail compilation. Missing or unsupported
contracts fail during compilation rather than leaving an unusable runtime query.
The function itself remains callable normally, and changing its signature updates
the generated interface. A clean rebuild does not rely on stale expression data.

## Starting points

- [Resource macro modules](../../../../source/builtin_macros/src/resource/)
- [Syntax integration](../../../../source/builtin_macros/src/syntax.rs)
- [Frontend attribute handling](../../../../source/rust_verify/src/attributes.rs)
- [Verifier and compilation integration](../../../../source/rust_verify/src/)
- [Build tasks](../../../../source/Makefile.toml)
