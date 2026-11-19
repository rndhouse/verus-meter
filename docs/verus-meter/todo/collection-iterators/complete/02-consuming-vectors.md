# 02 — Consuming vectors

Extend the [borrowed iteration work](01-borrowed-iteration.md) to
`for item in owners`, where `owners: Vec<T>`. Converting the vector to its
iterator transfers ownership of the backing allocation and its remaining
elements. Each successful advance transfers one element to the loop body.

## Work

- [x] Connect the [standard consuming iterator specification](../../../../../source/vstd/std_specs/vec.rs)
  to the memory model. Track the original backing capacity independently of the
  shrinking number of unvisited elements, including an empty vector with
  reserved capacity.
- [x] Preserve element order, allocation identity and separately owned children
  as items move into the body, into an output collection, or out through a
  return. Charge each live allocation once across the transfer.
- [x] Integrate iterator drop with the existing loop cleanup. On exhaustion,
  `break` or return, release the iterator's backing and the elements it still
  owns. Handle the current item according to where the body moved it.

## Completion checks

- [x] Complete the [checksum comparison](../README.md#acceptance-example), including
  the successful rerun under the larger allowance. Keep both versions runnable
  through the normal verifier.
- [x] Exercise early exit from a vector of owners such as `Vec<Box<Block>>`.
  Retain a yielded element and leave others unvisited. Check the peak during
  traversal and current storage after cleanup, including the surviving payload.
  A one-element vector with spare capacity also tests that yielding its last
  item does not prematurely release the backing while the body is executing.
- [x] Run the [project memory checks](../../../../../AGENTS.md#focused-memory-checks)
  and affected iterator, ownership-transfer and cleanup regressions.

Start with [iteration transfers](../../../../../source/vir/src/resource/memory/transfer/iteration.rs),
[iterator effects across calls](../../../../../source/vir/src/resource/memory/transfer/trace/iterators.rs)
and [ownership extraction tests](../../../../../source/rust_verify_test/tests/resource/memory/owned_extraction.rs).

## Validation

Implemented in `db16c2da1` on `feature/collection-iterators`. The streaming
checksum example verifies with a 164-model-byte section allowance. The staged
version fails with memory-budget diagnostics at the same allowance and verifies
when only the section allowance rises to 512 model bytes. Both passing examples
compiled and produced the same checksums.

The loop regressions check the last item's backing reservation, an empty
reserved iterator, cleanup on exhaustion and early exits, and ordered transfer
into a returned collection. They also check one-byte shortfalls for retained
storage during and after traversal.

The verifier rebuilt successfully. All 1,077 memory integration tests, 47
resource examples and 152 iterator, slice, array and reference tests passed.
The memory unit tests passed with 86 successes and one existing ignored test.
Rust formatting and strict Clippy passed for VIR and the resource tests. The
installed `verusfmt` could not parse the fork's `resources` clause.
