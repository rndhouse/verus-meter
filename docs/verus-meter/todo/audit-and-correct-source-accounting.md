# Audit and correct source memory accounting

Bring the verifier into line with the [source accounting policy](../accounting/README.md). Remove charges for implementation details while preserving every source-visible allocation and overlap. This audit covers sequential accounting. Concurrent proof work has its [own tracker](concurrent/README.md).

## What needs checking?

- [ ] Inventory the operations the verifier accepts, starting from frontend intrinsics and executable expression handling. Cover inline values and temporaries, borrowing and copying, owning containers, iteration, and calls. Group operations only when their storage effects agree.
- [ ] Apply shared principles across families. Identify what creates each charge, its size, who keeps it live, and what transfers or releases it. Add a detail page only when an operation needs its own accounting decision.
- [ ] Check library operations against their documented effects and executable user code against the source rules. Compare direct execution with helper, loop, and section accounting, then check the examples and docs.
- [ ] For missing operation support or ownership information, check the diagnostic with a generous budget. A missing rule must never silently grant zero cost.
- [ ] Record each discrepancy with a reproducer, the expected charge, and its resolution. Update the accounting page when a policy decision changes. Keep validation evidence with the fix in Git.

## Collection coverage

Check off each family after reviewing its supported operations. Follow the same storage across representations. Borrowing a view preserves the owner's charge, storing a copy charges its destination, and transferring ownership preserves live payloads. Add any further supported family found during the inventory.

- [ ] **Fixed integer arrays.** Check construction, copying, indexing, and borrowing an array as a slice. Compare a second live array with a view of the original. [Array copy example](../../../examples/resource/memory/expected-failures/array_copy.rs)
- [ ] **Shared and mutable slices.** Check stored slice references, length, indexed reads and writes, and supported iteration. Compare a view borrowed from an array with one borrowed from a vector. [Slice checks](../../../source/rust_verify_test/tests/resource/memory/storage_slices.rs)
- [ ] **Boxed slices.** Follow the handle, length-sized backing, and any owned children through conversion from a vector, borrowing, moves across helpers, and drop. [Boxed slice example](../../../examples/resource/memory/heap/boxed_slices.rs)
- [ ] **Vectors.** Check empty and reserved construction, push, pop, remove, indexing, borrowed views, and borrowed and consuming loops. Include a vector with owning elements and a helper that grows a borrowed vector. [Vector examples](../../../examples/resource/memory/README.md#vectors)

## Review through examples

- As each correction is validated, update its checklist item with the commit and links to every example changed. Flag those diffs for review while the audit is in progress.
- Show the before-and-after budget or verification result and name the storage that explains the difference. If an existing example demonstrates the correction as written, link it and report the result under its original budget.

## First corrections and controls

- [ ] **Borrowed iteration.** Remove charges for implicit iterator state and the reference used only to visit an item. Show that storing the item still costs a slot and consuming iteration still retains the input backing and unvisited payloads.
- [ ] **Streaming versus staging.** Check both versions under the same variable-length budget. One result slot per input plus the checksum allowance should cover the streaming loop. The split loop should exceed it because the staged bytes stay live. If the verifier still needs help proving one push per input, track that separately as loop-inference work.
- [ ] **Consuming conversion versus explicit replacement.** The boxed-slice conversion currently checks overlap with a possible internal replacement. Remove that charge. Keep a negative test where user code, directly or in a helper, creates a second buffer while the original is live. [Conversion implementation](../../../source/vir/src/resource/memory/boxed_slices.rs)
- [ ] **Reservation versus private growth.** Use the committed vector rule in `fc76adae3` as a control for pushes below and beyond a reservation and removals back to it. [Vector rules](../accounting/which-bytes-count/collections/vectors.md)
- [ ] **Move versus duplication.** Moving an owning buffer must fit with one backing. Creating an independent copy while the first is live must require both. For clone operations, check the specific operation's ownership semantics and support status.

## When is the audit complete?

- [ ] Check every supported family against the applicable rule and record how each accounting discrepancy was resolved. Distinguish committed fixes from pending edits.
- [ ] Derive the expected bytes independently and reuse existing tests or examples to check them. Add a test only when existing coverage misses a distinction that matters, such as an internal resize versus two explicitly live buffers. For a known exact peak, a budget one byte below it should fail on the budget check.
- [ ] Verify affected examples and run the repository's focused memory checks against the rebuilt verifier. Preserve earlier results against the revision they tested. The previous correctness and test reviews remain available in Git at `fc76adae3`.
