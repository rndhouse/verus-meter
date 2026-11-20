# Remove excess memory charges

Find and remove charges for compiler lowering and private library implementation details. Keep charging storage the Rust program creates, reserves, or keeps live under the agreed rules. Record missing operation support and proof limitations as separate work when they surface. [Source accounting rules](../accounting/README.md)

## Corrections

- [ ] **Borrowed iteration.** Remove charges for the generated iterator, its bookkeeping, and the reference used only to visit an item. Keep charges for a stored reference and for backing and unvisited payloads retained by a consuming loop. [Iteration rules](../accounting/which-bytes-count/iteration.md)
- [ ] **Boxed-slice conversion.** Remove the charge for a possible private replacement buffer in `into_boxed_slice()`. Check that the budget still includes both buffers when user code creates two and keeps them live together. [Boxed-slice rules](../accounting/which-bytes-count/collections/arrays-and-slices.md)

## Apply the same boundary across collections

- [ ] **Fixed integer arrays.** Check for hidden copies or temporaries in indexing and slice coercion. Preserve the cost of a second live array created by an explicit copy.
- [ ] **Shared and mutable slices.** Check supported access and iteration for hidden charges. Apply the same rule to views from arrays and vectors, preserving the owner's backing and any stored slice reference.
- [ ] **Boxed slices.** Check conversion and borrowing for charges beyond the source-level handle and owned storage.
- [ ] **Vectors.** Use the occupied-slot and explicit-reservation rule from `fc76adae3` as a baseline. Check that supported accesses, conversions, and loops apply the same boundary through helpers and resource sections. [Vector rules](../accounting/which-bytes-count/collections/vectors.md)

## Review through examples

- As each correction is validated, link its commit and flag every changed example for review. Show the before-and-after budget or verification result and identify the charge that disappeared.
- Use the streaming and staged checksum examples as a pair. The streaming version should fit the shared budget and the staged version should exceed it because it retains a second buffer. Check loop-length inference separately if the variable-length version still needs it.
- Reuse existing examples and tests where they show the distinction. Finish when the identified excess charges are removed across the supported collections and the affected examples confirm that source-visible storage still counts.
