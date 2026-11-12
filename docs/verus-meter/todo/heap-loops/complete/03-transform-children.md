# 3. Transform children during traversal

Builds on [task 1](01-compose-iteration-operations.md) and uses
[task 2](02-conditional-ownership-effects.md) for conditional transformations.

## Goal

Repeat a representable transformation of each child's ownership, including
changes to nested allocations and construction whose footprint varies with the
iteration.

## Supported boundary

A checked iteration can transform selected children through nested extraction,
fixed-field replacement, growth, conversion, and release before moving them to
another collection or dropping them. Source and destination child types may
differ. Generated blocks preserve every iteration's complete forest, including
nonuniform capacities and output order; their footprint is the sum of those
forests. Affine footprints also support symbolic iteration counts.

Iteration-dependent sizes can use admitted counter arithmetic or selected-child
length observations. Scalar proof ceilings are checked at the executable
operation and do not replace allocation descriptors. Intermediate original-input
regions and optional presence tags follow the same selection map, and temporary
iteration symbols are closed before export. Leaf-only helper results retain
inferred descriptors, including selected children from internal collections.

Repeated updates to the same persistent child remain in task 4; delegation of
incoming runtime subtrees remains in task 5. Payload-dependent sizes are
unsupported. Broader scalar-envelope inference belongs to task 6; ordinary
verification must still prove the generated bounds and intermediate peaks.

## Work

- [x] Represent a child transformation parametrically over its input forest and
  any supported iteration observations, using existing ownership operations.
- [x] Compose nested extraction, replacement, growth, and release within the
  child before insertion or drop.
- [x] Represent nonuniform generated child forests and their combined footprint
  without replacing them with one uniform child descriptor.
- [x] Preserve inferred child descriptors across leaf-only helper interfaces,
  including helpers that traverse an internal owning collection and return one
  selected child.
- [x] Preserve original-input provenance through intermediate regions; eliminate
  temporary iteration symbols before exporting the summary.
- [x] Identify and address expression-admission restrictions that prevent sizes
  from depending on supported iteration state. Keep unsupported dependencies
  explicit rather than widening syntax without an accounting model.

## Completion criteria

Tests cover transformed children with different initial capacities, nested child
release, changed children returned to a caller, and iteration-dependent sizes.
Check the temporary overlap as well as the final footprint. No temporary symbols
escape, no input allocation disappears from lifetime accounting, and unsupported
transformations reject with generous budgets.

## Starting points

- [Transfer dependency checks](../../../../../source/vir/src/resource/memory/transfer/trace/loops.rs)
- [Ownership forest operations](../../../../../source/vir/src/resource/memory/metadata/operations.rs)
- [Input-region accounting](../../../../../source/vir/src/resource/memory/provenance.rs)
- [Loop dependency regressions](../../../../../source/rust_verify_test/tests/resource/memory/loop_ownership.rs)
- [Transformed-child regressions](../../../../../source/rust_verify_test/tests/resource/memory/transformed_loops.rs)
