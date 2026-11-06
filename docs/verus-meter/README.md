# Verus Meter

Verus Meter extends Verus with resource contracts for Rust. Its current focus is
memory: a function declares a workspace budget, and verification catches changes
that exceed it alongside checking functional correctness.

```rust
fn work()
    mem_peak <= mem_size([u32; 4]),
{
    let buffer = [0u32; 4];
}
```

This contract allows room for one array. Adding a second array of that size in
the same scope would exceed the budget. The verifier accounts for storage
automatically; contracts add no runtime tracking.

Functions can refer to helper functions' budgets, divide work into independently
checked sections, and check the peak reached at a particular point. Conditional
contracts can give different inputs different allowances.

Bounds describe source-level workspace under a fixed memory model. Physical
stack size and heap usage are outside the current guarantee. Support is limited
to a subset of Rust, and unsupported operations are rejected in checked functions.

- [Memory contracts](model.md): how to write and understand the guarantees.
- [Examples](../../examples/resource/memory): complete programs with explanatory comments.
- [A deliberate violation](../../examples/resource/memory/expected-failures/array_copy.rs):
  an extra copy that makes verification fail.
