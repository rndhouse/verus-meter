# Source memory accounting

These pages record our design agreement about the memory bound Verus Meter should prove.

- The aim is to let programmers control algorithmic memory use through decisions they make in Rust source.
- A change to a compiler or library's private implementation should preserve the bound whenever the program and the operation's source-level effects stay the same.
- We use these rules to decide what the verifier should charge. Differences in current behavior belong in the [accounting audit](../todo/audit-and-correct-source-accounting.md).

## Rules

- [Which bytes count?](which-bytes-count/README.md) covers values, allocations, reservations, and library boundaries.
- [When do bytes count?](when-bytes-count/README.md) covers ownership, moves, and release.
- [How is peak calculated?](peak-calc/README.md) covers overlap across branches, loops, calls, and sections.
