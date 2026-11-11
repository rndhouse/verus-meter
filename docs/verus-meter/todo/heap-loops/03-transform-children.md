# 3. Transform children during traversal

Builds on [task 1](complete/01-compose-iteration-operations.md) and uses
[task 2](02-conditional-ownership-effects.md) for conditional transformations.

## Goal

Repeat a representable transformation of each child's ownership, including
changes to nested allocations and construction whose footprint varies with the
iteration.

## Current restriction

Transfers preserve whole children unchanged. Fresh repeated children must have
an iteration-independent footprint. Extracting a child, changing its ownership,
and reinserting it is not generally supported. Intermediate input regions from
nested extraction can also make a summary unrepresentable, even if the extracted
child is eventually dropped.

## Work

- [ ] Represent a child transformation parametrically over its input forest and
  any supported iteration observations, using existing ownership operations.
- [ ] Compose nested extraction, replacement, growth, and release within the
  child before insertion or drop.
- [ ] Represent nonuniform generated child forests and their combined footprint
  without replacing them with one uniform child descriptor.
- [ ] Preserve original-input provenance through intermediate regions; eliminate
  temporary iteration symbols before exporting the summary.
- [ ] Identify and address expression-admission restrictions that prevent sizes
  from depending on supported iteration state. Keep unsupported dependencies
  explicit rather than widening syntax without an accounting model.

## Completion criteria

Tests cover transformed children with different initial capacities, nested child
release, changed children returned to a caller, and iteration-dependent sizes.
Check the temporary overlap as well as the final footprint. No temporary symbols
escape, no input allocation disappears from lifetime accounting, and unsupported
transformations reject with generous budgets.

## Starting points

- [Transfer dependency checks](../../../../source/vir/src/resource/memory/transfer/trace/loops.rs)
- [Ownership forest operations](../../../../source/vir/src/resource/memory/metadata/operations.rs)
- [Input-region accounting](../../../../source/vir/src/resource/memory/provenance.rs)
- [Dependency rejection tests](../../../../source/rust_verify_test/tests/resource/memory/loop_ownership.rs)
