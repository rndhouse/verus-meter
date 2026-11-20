# When do bytes count?

## What keeps storage live?

- A local value occupies its slot while it is live. Merely passing its last read does not release the slot.
- An allocation starts counting when it is created or explicitly reserved. It remains live through moves, including a move into a field, a collection, or a function result.
- Borrowing preserves the original owner's charge. Dropping a borrow leaves the owner's storage live.

## What changes ownership or releases storage?

- Moving an owning value transfers its backing and owned children. Copying an inline array into another local creates a second array.
- Removing an element can transfer its payload to the result. The collection's own backing follows its documented rule. See the [collection index](README.md#collections).
- Dropping an owner, explicitly or at scope exit, releases the allocations it still owns exclusively. A moved-out child follows its new owner.
- On an early return or loop exit, account for the cleanup on that path. A consuming iterator retains its backing until it is dropped, even after yielding the last item.
