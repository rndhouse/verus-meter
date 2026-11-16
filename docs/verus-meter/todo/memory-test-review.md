# Memory test review

Review only tests added by this fork. In inherited files, review our added tests
and the wiring needed to run them; exclude inherited test cases.

## Process

Review the files alphabetically within each area, one file at a time. Check a
box only after reviewing the file and validating any fixes. Preliminary
inspection does not count as a completed review. Preserve detailed findings and
validation results in commit messages; this checklist tracks current status.

For each file, check distinct behavior, assertion strength, overlap, placement,
and maintenance cost. Recommend keep, strengthen, consolidate, move, or remove.
Record unresolved overlaps with later files and revisit them when reached.
Fix and commit problems found during review. Track unresolved work separately
below; do not accumulate a history of completed changes here.

When new test files are added, insert unchecked entries in alphabetical order.
Reopen a reviewed entry when substantive additions need review.

## Integration tests

Directory: `source/rust_verify_test/tests/resource/memory/`.
Progress: 48 of 48 files reviewed and validated.

- [x] [array_copy.rs](../../../source/rust_verify_test/tests/resource/memory/array_copy.rs)
- [x] [borrowed_vectors.rs](../../../source/rust_verify_test/tests/resource/memory/borrowed_vectors.rs)
- [x] [boxed_slices.rs](../../../source/rust_verify_test/tests/resource/memory/boxed_slices.rs)
- [x] [call_budgets.rs](../../../source/rust_verify_test/tests/resource/memory/call_budgets.rs)
- [x] [call_forests.rs](../../../source/rust_verify_test/tests/resource/memory/call_forests.rs)
- [x] [call_graph.rs](../../../source/rust_verify_test/tests/resource/memory/call_graph.rs)
- [x] [checkpoints.rs](../../../source/rust_verify_test/tests/resource/memory/checkpoints.rs)
- [x] [children.rs](../../../source/rust_verify_test/tests/resource/memory/children.rs)
- [x] [conditional.rs](../../../source/rust_verify_test/tests/resource/memory/conditional.rs)
- [x] [conditional_loops.rs](../../../source/rust_verify_test/tests/resource/memory/conditional_loops.rs)
- [x] [control_flow.rs](../../../source/rust_verify_test/tests/resource/memory/control_flow.rs)
- [x] [element_transfers.rs](../../../source/rust_verify_test/tests/resource/memory/element_transfers.rs)
- [x] [elements.rs](../../../source/rust_verify_test/tests/resource/memory/elements.rs)
- [x] [for_loops.rs](../../../source/rust_verify_test/tests/resource/memory/for_loops.rs)
- [x] [growth.rs](../../../source/rust_verify_test/tests/resource/memory/growth.rs)
- [x] [heap.rs](../../../source/rust_verify_test/tests/resource/memory/heap.rs)
- [x] [helper_control.rs](../../../source/rust_verify_test/tests/resource/memory/helper_control.rs)
- [x] [incoming_children.rs](../../../source/rust_verify_test/tests/resource/memory/incoming_children.rs)
- [x] [incoming_extraction.rs](../../../source/rust_verify_test/tests/resource/memory/incoming_extraction.rs)
- [x] [incoming_loops.rs](../../../source/rust_verify_test/tests/resource/memory/incoming_loops.rs)
- [x] [indexed_loops.rs](../../../source/rust_verify_test/tests/resource/memory/indexed_loops.rs)
- [x] [inference.rs](../../../source/rust_verify_test/tests/resource/memory/inference.rs)
- [x] [integers.rs](../../../source/rust_verify_test/tests/resource/memory/integers.rs)
- [x] [lifetimes.rs](../../../source/rust_verify_test/tests/resource/memory/lifetimes.rs)
- [x] [loop_ownership.rs](../../../source/rust_verify_test/tests/resource/memory/loop_ownership.rs)
- [x] [nested_growth.rs](../../../source/rust_verify_test/tests/resource/memory/nested_growth.rs)
- [x] [nested_ownership.rs](../../../source/rust_verify_test/tests/resource/memory/nested_ownership.rs)
- [x] [owned_extraction.rs](../../../source/rust_verify_test/tests/resource/memory/owned_extraction.rs)
- [x] [owned_replacement.rs](../../../source/rust_verify_test/tests/resource/memory/owned_replacement.rs)
- [x] [ownership.rs](../../../source/rust_verify_test/tests/resource/memory/ownership.rs)
- [x] [pattern_ownership.rs](../../../source/rust_verify_test/tests/resource/memory/pattern_ownership.rs)
- [x] [progress_loops.rs](../../../source/rust_verify_test/tests/resource/memory/progress_loops.rs)
- [x] [projections.rs](../../../source/rust_verify_test/tests/resource/memory/projections.rs)
- [x] [reachability.rs](../../../source/rust_verify_test/tests/resource/memory/reachability.rs)
- [x] [return_sharing.rs](../../../source/rust_verify_test/tests/resource/memory/return_sharing.rs)
- [x] [returns.rs](../../../source/rust_verify_test/tests/resource/memory/returns.rs)
- [x] [sections.rs](../../../source/rust_verify_test/tests/resource/memory/sections.rs)
- [x] [size_queries.rs](../../../source/rust_verify_test/tests/resource/memory/size_queries.rs)
- [x] [spec_functions.rs](../../../source/rust_verify_test/tests/resource/memory/spec_functions.rs)
- [x] [storage.rs](../../../source/rust_verify_test/tests/resource/memory/storage.rs)
- [x] [storage_budgets.rs](../../../source/rust_verify_test/tests/resource/memory/storage_budgets.rs)
- [x] [storage_calls.rs](../../../source/rust_verify_test/tests/resource/memory/storage_calls.rs)
- [x] [storage_initialization.rs](../../../source/rust_verify_test/tests/resource/memory/storage_initialization.rs)
- [x] [storage_model.rs](../../../source/rust_verify_test/tests/resource/memory/storage_model.rs)
- [x] [storage_slices.rs](../../../source/rust_verify_test/tests/resource/memory/storage_slices.rs)
- [x] [storage_structs.rs](../../../source/rust_verify_test/tests/resource/memory/storage_structs.rs)
- [x] [transformed_loops.rs](../../../source/rust_verify_test/tests/resource/memory/transformed_loops.rs)
- [x] [vectors.rs](../../../source/rust_verify_test/tests/resource/memory/vectors.rs)

## Harness and shared assertions

- [x] [resource.rs](../../../source/rust_verify_test/tests/resource.rs)
- [x] [mod.rs](../../../source/rust_verify_test/tests/resource/memory/mod.rs)
- [x] [support.rs](../../../source/rust_verify_test/tests/resource/memory/support.rs)

## Remaining fork memory coverage

After the integration suite, review these areas. Check each area only after
reviewing all applicable fork additions within it.

- [x] Internal unit tests under `source/vir/src/resource/memory/` (42 tests in 10 files).
- [ ] Parser tests under `dependencies/syn/tests/resource/memory/` and their entry point.
- [ ] The two memory prettyprinter tests added to `dependencies/prettyplease/tests/test.rs`.
- [ ] Executable examples under `examples/resource/memory/`, including expected failures.
- [ ] Fork additions to `source/rust_verify_test/tests/examples.rs` that register and run memory examples.

## Open work

Keep only unresolved follow-up tasks and cross-file overlap questions here.
Remove resolved items; distinguish tentative candidates from confirmed duplicates.

None from the completed file reviews.
