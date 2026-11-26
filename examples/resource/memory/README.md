# Memory examples

These examples prove memory bounds under the source-level model, alongside
ordinary Verus correctness checks. Start with the basics, then explore a topic.

A single-file example uses `name.rs`. For an example with several files, put
`main` in `name/mod.rs` and declare its sibling modules there. The example
runner tests the directory as one program.

## Basics

- [Scope reuse](basics/storage.rs): share an allowance across scopes, branches, and loops.
- [Integer types](basics/integers.rs): check arithmetic safety and memory use together.
- [Returning buffers](basics/returns.rs): return a buffer without counting its storage twice.
- [Optional results](basics/options.rs): retain a result after releasing its collection.

## Contracts

- [Runtime queries](contracts/runtime_query.rs): query a declared allowance before
  allocating, using an explicit model-byte budget and a positive byte count. See
  the [run instructions](../../../source/verus-meter/runtime/README.md#run-the-example)
  for admission and rejection paths.
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
- [Buffer collection](heap/loops/buffer_collection.rs): compute a memory budget from the requested number of heap buffers while retaining a local array.
- [For-loop construction](heap/loops/for_construction.rs): collect buffers with an integer range and account for iterator state separately.
- The streaming loop peaks while computing the second checksum. The first result and the current decoded block are live alongside the checksum helper. [Streaming checksums](heap/loops/streaming_checksums.rs)
- Staging adds two decoded blocks' worth of backing storage at that same call. The example derives both the section bound and the enclosing function's bound. [Staged checksums](heap/loops/staged_checksums.rs)
- [Partial transfers](heap/loops/partial_transfers.rs): move batches of children and release the source independently.
- [Peak overlap](heap/loops/peak_overlap.rs): release extracted work buffers while collecting results within an input-dependent budget.

## Vectors

- [Reserved capacity](vectors/vectors.rs): prove that every addition fits the reservation.
- [Borrowing vectors](vectors/vector_helpers.rs): let helpers use an existing reservation.
- [Returning vectors](vectors/vector_returns.rs): preserve a reservation when returning a buffer.
- [Growing vectors](vectors/vector_growth.rs): budget for the vector handle and its occupied or explicitly reserved slots.
- [Nested growth](vectors/nested_growth.rs): grow related buffers independently.
- [Owning collections](vectors/owning_collections.rs): include allocations owned by the elements.
- [Helper collections](vectors/helper_collections.rs): retain child reservations through counted construction and reuse them after a call.
- [Indexed owners](vectors/indexed_owners.rs): account for changes to individual owning elements.
- [Element transfers](vectors/element_transfers.rs): extract owning elements and reuse their storage across loop iterations.

## Concurrency

- [Bounding peak memory with a mutex](concurrent/mutex_bounds_peak.rs): prove that at most one scratch buffer is live at a time. Each worker allocates and frees its own buffer while holding the same mutex.
- [Detecting buffer overlap after unlocking (expected failure)](concurrent/expected-failures/unlock_before_drop.rs): one worker can still own its buffer when the next worker allocates. Verus Meter rejects a peak bound that allows room for only one buffer.
- [Tracking worker allocations in a shared collection](concurrent/retained_buffers.rs): each of four workers moves its buffer into a shared vector. Verus Meter accounts for all four buffers even after every worker has finished and been joined.
- [Counting uncollected worker results in peak memory](concurrent/worker_result.rs): a finished worker's returned buffer stays live until the coordinator collects it. Another worker can allocate its own buffer under the same mutex in the meantime, so the peak bound must cover both.
- [Bounding peak memory with a semaphore](concurrent/semaphore.rs): four workers can each request 4 KiB of scratch, yet two permits keep their combined scratch at or below 8 KiB. Verus Meter proves the bound for any supported worker count, permit count, and buffer capacity.
- [Custom mutex](concurrent/custom_mutex/mod.rs): use a [verified lock protocol](concurrent/custom_mutex/protocol.rs) to prove that workers share one scratch allowance.

## Algorithms

- [Insertion sort](algorithms/insertion_sort.rs): prove sorting correctness within a fixed memory allowance.
- [Calling the sorter](algorithms/calls.rs): include a helper's allowance in its caller's budget.
- [Sorting a struct](algorithms/structs.rs): account for stored data and the work needed to sort it.

## Deliberate violations

These programs intentionally fail verification. Their comments identify the
operation or checkpoint that exceeds its allowance.

- [Array copy](expected-failures/array_copy.rs): keep a copy without budgeting for its storage.
- [Checkpoint](expected-failures/checkpoint.rs): assert too small a bound on an earlier peak.
- [Overlapping allocations](expected-failures/heap_overlap.rs): allocate an extra box beyond an input-dependent collection budget.
- [Loop allocation overlap](expected-failures/loop_peak_overlap.rs): retain an extracted buffer while reserving its replacement on later iterations.
- [Staged checksums under the streaming allowance](expected-failures/staged_checksums.rs): keep the same section allowance while adding a vector of decoded blocks.
- [Returned allocations](expected-failures/heap_returns.rs): retain allocations across repeated helper calls.
- [Vector growth](expected-failures/vector_growth.rs): grow beyond the reserved buffer without extra allowance.
