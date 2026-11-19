# 01 — Borrowed slices and vectors

Verify direct iteration over `blocks: &[T]` and `&blocks` for
`blocks: Vec<T>`. In both cases the yielded item is `&T`. The original owner
retains its backing allocation and any allocations owned by its elements.

## Work

- [x] Connect the standard borrowed `IntoIterator` and slice iterator operations
  to the existing checked `for` loop by compiler identity. Reuse the sequence
  and progress facts in the [slice](../../../../../source/vstd/std_specs/slice.rs)
  and [vector](../../../../../source/vstd/std_specs/vec.rs) specifications.
- [x] Model live iterator state, the yielded reference and temporaries. Preserve
  the link to the original element across a checked helper call. Taking or
  dropping the reference must neither duplicate nor release its pointee's charge.
- [x] Use the existing loop entry, advancement, exhaustion and exit checks.
  Derive the accounting facts for the streaming checksum loop from the checked
  operations and prove the generated obligations.

## Completion checks

- [x] Verify the streaming half of the [checksum example](../README.md#acceptance-example)
  under its derived section budget. Exercise both borrowed entry points through
  ordinary source syntax.
- [x] Check an empty vector with reserved capacity and a traversal that breaks
  early. Verify the vector remains usable afterward and its backing and owned
  children still count against the owner's budget. Tighten a bound to confirm
  the checker detects those live bytes.
- [x] Run the [project memory checks](../../../../../AGENTS.md#focused-memory-checks)
  and the affected iterator and reference regressions.

Start with [iterator accounting](../../../../../source/vir/src/resource/memory/iterators.rs),
[loop adaptation](../../../../../source/vir/src/resource/memory/for_loops.rs) and
[source-level loop tests](../../../../../source/rust_verify_test/tests/resource/memory/for_loops.rs).

## Validation

Implemented in `e32a2341c` on `feature/collection-iterators`. The executable
`examples/resource/memory/heap/loops/streaming_checksums.rs` verifies the
164-model-byte streaming section and produces the expected checksums. The loop
tests cover both borrowed entry points, empty reserved storage, early exit and
retention of a borrowed element's backing allocation.

The verifier and vstd rebuilt successfully. All 1,072 memory integration tests,
45 resource examples and 152 iterator, slice, array and reference tests passed.
The memory unit tests passed with 86 successes and one existing ignored test.
Rust formatting and strict Clippy passed for VIR and the resource tests.
