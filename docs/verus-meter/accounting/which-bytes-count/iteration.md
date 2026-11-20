# Iteration

- In a borrowed loop, accessing the current item adds no charge for the implicit iterator, its bookkeeping, or the reference supplied just to visit the item.
- Storing the item or its reference in an output collection charges the destination slot.
- A mutable item binding can store another reference and occupies a slot.
- A consuming loop charges the source item binding and retains the input's backing and unvisited payloads. The cursor and temporary dispatch slots add no charge.

## Why can splitting a loop increase peak?

- A streaming checksum loop can append each result directly to its output. The processed input byte needs no staging slot.
- If the first loop stores the bytes and the second borrows that collection to compute the results, the staged bytes stay live as the output grows.
