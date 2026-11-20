# How is peak calculated?

- At each point on an allowed execution, add the modeled bytes live together. The contract must cover the greatest such total on every allowed execution.
- A check of current memory can fall after a drop. A check of peak memory still includes the earlier high point.

## What overlaps?

- **Branches.** Each execution takes its own path. Mutually exclusive workspaces can use the same allowance.
- **Loops.** Iterations can reuse released scratch space. Values retained by later iterations continue to count.
- **Calls.** Combine the callee's declared allowance with the caller storage that stays live across the call. Declared slack counts when composing contracts. Passing an owner to a helper preserves the allocation's identity.
- **Sections.** Take the allowance at section entry. The enclosing scope pays for storage already live and the section's allowance. Growth of an enclosing collection inside the section remains with its owner on exit.

## Examples

- [Overlapping and separate scopes](../../../examples/resource/memory/basics/storage.rs)
- [Splitting a streaming loop](which-bytes-count/iteration.md#why-can-splitting-a-loop-increase-peak)
