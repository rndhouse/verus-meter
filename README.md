# Verus Meter

Verus Meter is an experimental fork of [Verus](https://github.com/verus-lang/verus)
that adds resource contracts for Rust. Its current focus is memory: a function declares a workspace budget, and verification catches changes
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
contracts can give different inputs different allowances and preserve them through
helper calls. Boxes and vectors without growth can also carry checked
heap allowances; vector budgets can scale with a runtime capacity. Helpers can
return values, including `Option`, with result storage counted once across the call.
Heap ownership can pass between helpers; moving a value into the result transfers
its charge, and allocations remain charged until their new owner releases them.

Bounds describe declared storage and supported heap objects under a fixed memory
model. Physical stack size and allocator overhead are outside the guarantee.
Support is limited to a subset of Rust; unsupported operations are rejected in
checked functions.

- [Memory contracts](docs/verus-meter/model.md): how to write and understand the guarantees.
- [Examples](examples/resource/memory): complete programs with explanatory comments.
- [A deliberate violation](examples/resource/memory/expected-failures/array_copy.rs):
  an extra copy that makes verification fail.
- [Maintaining the fork](docs/verus-meter/integration.md): integration hooks and rebase checks.

The [memory verifier tests](source/rust_verify_test/tests/resource/memory)
run together from `source/`:

```sh
cargo test --release -p rust_verify_test --test resource memory:: -- --test-threads=2
```

Replace `memory::` with a topic such as `memory::ownership::` to select one suite.
