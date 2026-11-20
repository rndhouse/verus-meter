# Source memory accounting

Verus Meter bounds the source-level storage a Rust program keeps live. These pages define the accounting policy. The current verifier still charges some operations more than the policy requires.

## Rules

- [Which bytes count?](which-bytes-count.md) covers values, allocations, reservations, and library boundaries.
- [When do bytes count?](when-bytes-count.md) covers ownership, moves, and release.
- [How is peak calculated?](how-peak-is-calculated.md) covers overlap across branches, loops, calls, and sections.

## Collections

- [Arrays and slices](collections/arrays-and-slices.md) covers inline elements, borrowed views, and boxed slices.
- [Vectors](collections/vectors.md) covers explicitly reserved slots, occupied slots, and owned elements.

For contract syntax, see the [contract guide](../../model.md). For known discrepancies, see the [accounting audit](../todo/audit-and-correct-source-accounting.md).
