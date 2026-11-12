# Memory examples

These examples prove memory bounds under the source-level model, alongside
ordinary Verus correctness checks. Start with the basics, then explore a topic.

## Basics

- [Scope reuse](basics/storage.rs): share an allowance across scopes, branches, and loops.
- [Integer types](basics/integers.rs): check arithmetic safety and memory use together.
- [Returning buffers](basics/returns.rs): return a buffer without counting its storage twice.
- [Optional results](basics/options.rs): retain a result after releasing its collection.

## Contracts

- [Conditional budgets](contracts/conditional.rs): give different inputs different allowances.
- [Budgets across calls](contracts/call_budgets.rs): preserve input-specific allowances through helpers.
- [Named formulas](contracts/spec_budgets.rs): reuse a spec function to describe memory needs.
- [Returned formulas](contracts/function_budgets.rs): build a reusable formula from chosen parameters.
- [Sections](contracts/sections.rs): check parts of an operation independently.
- [Checkpoints](contracts/checkpoints.rs): compare live memory with the peak reached so far.

## Heap

- [Heap buffers](heap/heap.rs): release one buffer before reusing its allowance.
- [Ownership transfers](heap/ownership.rs): preserve allocation charges across helper calls.
- [Nested ownership](heap/nested_ownership.rs): account for related allocations under one owner.
- [Child transfers](heap/child_transfers.rs): move and replace owning fields.
- [Boxed slices](heap/boxed_slices.rs): turn a vector into a fixed-length owning buffer.

### Loops

Budgets use named storage types and memory formulas. Collection-length bounds
are included only where needed for memory verification.

- [Batched construction](heap/loops/batched_construction.rs): derive an input-dependent budget while collecting two buffers per batch.
- [Partial transfers](heap/loops/partial_transfers.rs): move batches of children and release the source independently.
- [Peak overlap](heap/loops/peak_overlap.rs): release extracted work buffers while collecting results within an input-dependent budget.

## Vectors

- [Reserved capacity](vectors/vectors.rs): prove that every addition fits the reservation.
- [Borrowing vectors](vectors/vector_helpers.rs): let helpers use an existing reservation.
- [Returning vectors](vectors/vector_returns.rs): preserve a reservation when returning a buffer.
- [Growing vectors](vectors/vector_growth.rs): budget for old and replacement buffers together.
- [Nested growth](vectors/nested_growth.rs): grow related buffers independently.
- [Owning collections](vectors/owning_collections.rs): include allocations owned by the elements.
- [Helper collections](vectors/helper_collections.rs): retain child reservations through counted construction and reuse them after a call.
- [Indexed owners](vectors/indexed_owners.rs): account for changes to individual owning elements.
- [Element transfers](vectors/element_transfers.rs): extract owning elements and reuse their storage across loop iterations.

## Algorithms

- [Insertion sort](algorithms/insertion_sort.rs): prove sorting correctness within a fixed memory allowance.
- [Calling the sorter](algorithms/calls.rs): include a helper's allowance in its caller's budget.
- [Sorting a struct](algorithms/structs.rs): account for stored data and the work needed to sort it.

## Deliberate violations

These programs intentionally fail verification. Their comments identify the
operation or checkpoint that exceeds its allowance.

- [Array copy](expected-failures/array_copy.rs): keep a copy without budgeting for its storage.
- [Checkpoint](expected-failures/checkpoint.rs): assert too small a bound on an earlier peak.
- [Overlapping allocations](expected-failures/heap_overlap.rs): keep two heap buffers within room for one.
- [Loop allocation overlap](expected-failures/loop_peak_overlap.rs): retain an extracted buffer while reserving its replacement on later iterations.
- [Returned allocations](expected-failures/heap_returns.rs): retain allocations across repeated helper calls.
- [Returned buffers](expected-failures/returned_buffers.rs): keep more results than the budget allows.
- [Vector growth](expected-failures/vector_growth.rs): grow beyond the reserved buffer without extra allowance.
