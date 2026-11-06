# First experiment: lexical storage reuse

Historical milestone: **lexical-slots-v0**. See [model.md](model.md) for the
current rules, supported subset, implementation map, and run commands.

This experiment established native resource syntax and a structural checker in
the Verus fork. Its question was whether changing lexical overlap could change
an enforced budget without relying on compiler stack layout.

```rust
fn example()
    resources peak_local_storage_bytes <= 516,
{
    { let first = [0u32; 64]; }
    { let second = [0u32; 64]; }
}
```

The initial subset covered `u32`, `bool`, unit, fixed `u32` arrays, named locals,
assignments, comparisons, branches, and while loops. Calls, references, indexing,
arithmetic, and custom datatypes were rejected. Ghost code was erased from the
accounting. These restrictions described that milestone, not the current subset.

## Result and design decision

The conservative initializer rule reserves the destination before evaluating
its initializer, retaining both until handoff. One 64-element array therefore
peaks at `256 + 256 + 4 = 516` model bytes. Successive nested scopes reuse that
storage; two arrays in the same scope peak at `256 + 256 + 256 + 4 = 772`.

The [example](../../examples/resource/memory/resource_storage.rs) and regression tests preserve
those distinctions, including exact and insufficient budgets, copying, shadowing,
parameter charges, and ghost erasure. Array-repeat syntax receives compiler
provenance; explicitly calling its helper does not receive the same exemption.

The checker was deliberately structural rather than an SMT-generated counter.
That decision and the lexical/initializer rules carry forward in the
[current model](model.md). Arithmetic and slice support followed in the
[second experiment](slices-and-sort.md); [call composition](calls.md) followed next.

## Validation

Validated on 2026-11-05:

- `cargo make build` passed, including 2,226 standard-library verification checks.
- All 36 `resource_storage` integration tests passed.
- 373 existing tests passed across `basic`, `functions`, `loops`, `size_of`,
  `mut_refs_slices_arrays`, `arrays`, `erase`, and `modes`; five tests were ignored
  by upstream annotations. The complete Verus test suite was not run.
- All four parser tests in `dependencies/syn/tests/test_resources.rs` passed,
  covering clause round-tripping, erasure, malformed budgets, and where clauses.
- `examples/resource/memory/resource_storage.rs` verified with seven checks and zero errors,
  compiled with `--compile`, and its executable ran successfully.
- Rust formatting checks, `git diff --check`, and syntax-codegen reproducibility
  passed.
