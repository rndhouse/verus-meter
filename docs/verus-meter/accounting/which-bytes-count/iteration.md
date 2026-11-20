# Iteration

- In a borrowed loop, accessing the current item adds no charge for the implicit iterator, its bookkeeping, or the reference supplied just to visit the item.
- Storing the item or its reference in an output collection charges the destination slot. A consuming loop can also keep the input's backing and unvisited payloads live.
- The verifier currently charges hidden iteration storage. The [audit](../../todo/remove-excess-memory-charges.md) tracks the correction.

## Why can splitting a loop increase peak?

- A streaming checksum loop can append each result directly to its output. The processed input byte needs no staging slot.
- If the first loop stores the bytes and the second borrows that collection to compute the results, the staged bytes stay live as the output grows.
