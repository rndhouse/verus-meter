# 01 — Borrowed slices and vectors

Verify direct iteration over `blocks: &[T]` and `&blocks` for
`blocks: Vec<T>`. In both cases the yielded item is `&T`. The original owner
retains its backing allocation and any allocations owned by its elements.

## Work

- [ ] Connect the standard borrowed `IntoIterator` and slice iterator operations
  to the existing checked `for` loop by compiler identity. Reuse the sequence
  and progress facts in the [slice](../../../../source/vstd/std_specs/slice.rs)
  and [vector](../../../../source/vstd/std_specs/vec.rs) specifications.
- [ ] Model live iterator state, the yielded reference and temporaries. Preserve
  the link to the original element across a checked helper call. Taking or
  dropping the reference must neither duplicate nor release its pointee's charge.
- [ ] Use the existing loop entry, advancement, exhaustion and exit checks.
  Derive the accounting facts for the streaming checksum loop from the checked
  operations and prove the generated obligations.

## Completion checks

- [ ] Verify the streaming half of the [checksum example](README.md#acceptance-example)
  under its derived section budget. Exercise both borrowed entry points through
  ordinary source syntax.
- [ ] Check an empty vector with reserved capacity and a traversal that breaks
  early. Verify the vector remains usable afterward and its backing and owned
  children still count against the owner's budget. Tighten a bound to confirm
  the checker detects those live bytes.
- [ ] Run the [project memory checks](../../../../AGENTS.md#focused-memory-checks)
  and the affected iterator and reference regressions.

Start with [iterator accounting](../../../../source/vir/src/resource/memory/iterators.rs),
[loop adaptation](../../../../source/vir/src/resource/memory/for_loops.rs) and
[source-level loop tests](../../../../source/rust_verify_test/tests/resource/memory/for_loops.rs).
