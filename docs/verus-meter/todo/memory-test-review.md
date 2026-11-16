# Memory test review

Review only tests added by this fork. In inherited files, review our added tests
and the wiring needed to run them; exclude inherited test cases.

## Process

Review the integration test files alphabetically, one file at a time. Check a
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
Progress: 3 of 48 files reviewed. Next: `call_budgets.rs`.

- [x] [array_copy.rs](../../../source/rust_verify_test/tests/resource/memory/array_copy.rs)
- [x] [borrowed_vectors.rs](../../../source/rust_verify_test/tests/resource/memory/borrowed_vectors.rs)
- [x] [boxed_slices.rs](../../../source/rust_verify_test/tests/resource/memory/boxed_slices.rs)
- [ ] [call_budgets.rs](../../../source/rust_verify_test/tests/resource/memory/call_budgets.rs)
- [ ] [call_forests.rs](../../../source/rust_verify_test/tests/resource/memory/call_forests.rs)
- [ ] [call_graph.rs](../../../source/rust_verify_test/tests/resource/memory/call_graph.rs)
- [ ] [checkpoints.rs](../../../source/rust_verify_test/tests/resource/memory/checkpoints.rs)
- [ ] [children.rs](../../../source/rust_verify_test/tests/resource/memory/children.rs)
- [ ] [conditional.rs](../../../source/rust_verify_test/tests/resource/memory/conditional.rs)
- [ ] [conditional_loops.rs](../../../source/rust_verify_test/tests/resource/memory/conditional_loops.rs)
- [ ] [control_flow.rs](../../../source/rust_verify_test/tests/resource/memory/control_flow.rs)
- [ ] [element_transfers.rs](../../../source/rust_verify_test/tests/resource/memory/element_transfers.rs)
- [ ] [elements.rs](../../../source/rust_verify_test/tests/resource/memory/elements.rs)
- [ ] [for_loops.rs](../../../source/rust_verify_test/tests/resource/memory/for_loops.rs)
- [ ] [growth.rs](../../../source/rust_verify_test/tests/resource/memory/growth.rs)
- [ ] [heap.rs](../../../source/rust_verify_test/tests/resource/memory/heap.rs)
- [ ] [helper_control.rs](../../../source/rust_verify_test/tests/resource/memory/helper_control.rs)
- [ ] [incoming_children.rs](../../../source/rust_verify_test/tests/resource/memory/incoming_children.rs)
- [ ] [incoming_extraction.rs](../../../source/rust_verify_test/tests/resource/memory/incoming_extraction.rs)
- [ ] [incoming_loops.rs](../../../source/rust_verify_test/tests/resource/memory/incoming_loops.rs)
- [ ] [indexed_loops.rs](../../../source/rust_verify_test/tests/resource/memory/indexed_loops.rs)
- [ ] [inference.rs](../../../source/rust_verify_test/tests/resource/memory/inference.rs)
- [ ] [integers.rs](../../../source/rust_verify_test/tests/resource/memory/integers.rs)
- [ ] [lifetimes.rs](../../../source/rust_verify_test/tests/resource/memory/lifetimes.rs)
- [ ] [loop_ownership.rs](../../../source/rust_verify_test/tests/resource/memory/loop_ownership.rs)
- [ ] [nested_growth.rs](../../../source/rust_verify_test/tests/resource/memory/nested_growth.rs)
- [ ] [nested_ownership.rs](../../../source/rust_verify_test/tests/resource/memory/nested_ownership.rs)
- [ ] [owned_extraction.rs](../../../source/rust_verify_test/tests/resource/memory/owned_extraction.rs)
- [ ] [owned_replacement.rs](../../../source/rust_verify_test/tests/resource/memory/owned_replacement.rs)
- [ ] [ownership.rs](../../../source/rust_verify_test/tests/resource/memory/ownership.rs)
- [ ] [pattern_ownership.rs](../../../source/rust_verify_test/tests/resource/memory/pattern_ownership.rs)
- [ ] [progress_loops.rs](../../../source/rust_verify_test/tests/resource/memory/progress_loops.rs)
- [ ] [projections.rs](../../../source/rust_verify_test/tests/resource/memory/projections.rs)
- [ ] [reachability.rs](../../../source/rust_verify_test/tests/resource/memory/reachability.rs)
- [ ] [return_sharing.rs](../../../source/rust_verify_test/tests/resource/memory/return_sharing.rs)
- [ ] [returns.rs](../../../source/rust_verify_test/tests/resource/memory/returns.rs)
- [ ] [sections.rs](../../../source/rust_verify_test/tests/resource/memory/sections.rs)
- [ ] [size_queries.rs](../../../source/rust_verify_test/tests/resource/memory/size_queries.rs)
- [ ] [spec_functions.rs](../../../source/rust_verify_test/tests/resource/memory/spec_functions.rs)
- [ ] [storage.rs](../../../source/rust_verify_test/tests/resource/memory/storage.rs)
- [ ] [storage_budgets.rs](../../../source/rust_verify_test/tests/resource/memory/storage_budgets.rs)
- [ ] [storage_calls.rs](../../../source/rust_verify_test/tests/resource/memory/storage_calls.rs)
- [ ] [storage_initialization.rs](../../../source/rust_verify_test/tests/resource/memory/storage_initialization.rs)
- [ ] [storage_model.rs](../../../source/rust_verify_test/tests/resource/memory/storage_model.rs)
- [ ] [storage_slices.rs](../../../source/rust_verify_test/tests/resource/memory/storage_slices.rs)
- [ ] [storage_structs.rs](../../../source/rust_verify_test/tests/resource/memory/storage_structs.rs)
- [ ] [transformed_loops.rs](../../../source/rust_verify_test/tests/resource/memory/transformed_loops.rs)
- [ ] [vectors.rs](../../../source/rust_verify_test/tests/resource/memory/vectors.rs)

## Harness and shared assertions

- [ ] [resource.rs](../../../source/rust_verify_test/tests/resource.rs)
- [ ] [mod.rs](../../../source/rust_verify_test/tests/resource/memory/mod.rs)
- [ ] [support.rs](../../../source/rust_verify_test/tests/resource/memory/support.rs)

## Remaining fork memory coverage

After the integration suite, review these areas. Check each area only after
reviewing all applicable fork additions within it.

- [ ] Internal unit tests under `source/vir/src/resource/memory/`.
- [ ] Parser tests under `dependencies/syn/tests/resource/memory/` and their entry point.
- [ ] The two memory prettyprinter tests added to `dependencies/prettyplease/tests/test.rs`.
- [ ] Executable examples under `examples/resource/memory/`, including expected failures.
- [ ] Fork additions to `source/rust_verify_test/tests/examples.rs` that register and run memory examples.

## Open work

Keep only unresolved follow-up tasks and cross-file overlap questions here.
Remove resolved items; distinguish tentative candidates from confirmed duplicates.

None from the completed file reviews.
