# Branches and loops

- **Branches.** Each execution takes its own path. Mutually exclusive workspaces can use the same allowance.
- **Loops.** Iterations can reuse released scratch space. Values retained by later iterations continue to count.

## Examples

- [Overlapping and separate scopes](../../../../examples/resource/memory/basics/storage.rs)
- [Splitting a streaming loop](../which-bytes-count/iteration.md#why-can-splitting-a-loop-increase-peak)
