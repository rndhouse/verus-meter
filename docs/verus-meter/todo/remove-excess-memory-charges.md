# Remove excess memory charges

Find and remove charges for compiler lowering and private library implementation details. Keep charging storage the Rust program creates, reserves, or keeps live under the agreed rules. Record missing operation support and proof limitations as separate work when they surface. [Source accounting rules](../accounting/README.md)

## Corrections

- [x] **Collection iteration.** In `a455a4268`, the checksum examples share a 183-byte section budget, down from 231. Streaming verifies and staging still exceeds the budget. Checks cover stored references, consumed item slots, and backing retained through the last visit. [Streaming checksum](../../../examples/resource/memory/heap/loops/streaming_checksums.rs) · [Staged checksum](../../../examples/resource/memory/expected-failures/staged_checksums.rs)
- [x] **Boxed-slice conversion.** In `a455a4268`, conversion verifies at 56 bytes, down from 64 after removing the private replacement charge. An explicit second buffer still causes a budget violation. [Boxed-slice example](../../../examples/resource/memory/heap/boxed_slices.rs) · [Explicit overlap](../../../examples/resource/memory/expected-failures/heap_overlap.rs)

## Apply the same boundary across collections

- [x] **Fixed integer arrays.** Indexing and coercion preserve the backing. A second live array created by a copy still costs its full size.
- [x] **Shared and mutable slices.** Array and vector views preserve the owner’s charge. A stored slice reference costs its own slot.
- [x] **Boxed slices.** The conversion and borrowing checks cover the handles, retained elements, and helper calls.
- [x] **Vectors.** The occupied-slot and explicit-reservation rule from `fc76adae3` holds across the checked accesses, conversions, loops, helpers, and resource sections. [Vector rules](../accounting/which-bytes-count/collections/vectors.md)

## Review through examples

- As each correction is validated, link its commit and flag every changed example for review. Show the before-and-after budget or verification result and identify the charge that disappeared.
- Separate proof follow-up. The variable-length checksum still needs inference that the loop pushes one result per input.
- Reuse existing examples and tests where they show the distinction. Finish when the identified excess charges are removed across the supported collections and the affected examples confirm that source-visible storage still counts.
