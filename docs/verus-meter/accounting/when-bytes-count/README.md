# When do bytes count?

## Principles

- A local value occupies its slot while it is live. Merely passing its last read does not release the slot.
- An allocation starts counting when it is created or explicitly reserved. It remains live through moves, including a move into a field, a collection, or a function result.
- Borrowing preserves the original owner's charge. Dropping a borrow leaves the owner's storage live.
- Storage is released when its modeled lifetime ends. Cleanup follows the path that executes.

## Specific rules

- [Ownership transfers and cleanup](transfers-and-cleanup.md)
