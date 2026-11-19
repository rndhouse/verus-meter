# 02 — Consuming vectors

Extend the [borrowed iteration work](complete/01-borrowed-iteration.md) to
`for item in owners`, where `owners: Vec<T>`. Converting the vector to its
iterator transfers ownership of the backing allocation and its remaining
elements. Each successful advance transfers one element to the loop body.

## Work

- [ ] Connect the [standard consuming iterator specification](../../../../source/vstd/std_specs/vec.rs)
  to the memory model. Track the original backing capacity independently of the
  shrinking number of unvisited elements, including an empty vector with
  reserved capacity.
- [ ] Preserve element order, allocation identity and separately owned children
  as items move into the body, into an output collection, or out through a
  return. Charge each live allocation once across the transfer.
- [ ] Integrate iterator drop with the existing loop cleanup. On exhaustion,
  `break` or return, release the iterator's backing and the elements it still
  owns. Handle the current item according to where the body moved it.

## Completion checks

- [ ] Complete the [checksum comparison](README.md#acceptance-example), including
  the successful rerun under the larger allowance. Keep both versions runnable
  through the normal verifier.
- [ ] Exercise early exit from a vector of owners such as `Vec<Box<Block>>`.
  Retain a yielded element and leave others unvisited. Check the peak during
  traversal and current storage after cleanup, including the surviving payload.
  A one-element vector with spare capacity also tests that yielding its last
  item does not prematurely release the backing while the body is executing.
- [ ] Run the [project memory checks](../../../../AGENTS.md#focused-memory-checks)
  and affected iterator, ownership-transfer and cleanup regressions.

Start with [iteration transfers](../../../../source/vir/src/resource/memory/transfer/iteration.rs),
[iterator effects across calls](../../../../source/vir/src/resource/memory/transfer/trace/iterators.rs)
and [ownership extraction tests](../../../../source/rust_verify_test/tests/resource/memory/owned_extraction.rs).
