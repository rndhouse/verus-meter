# Ownership transfers and cleanup

- Moving an owning value transfers its backing and owned children. Copying an inline array into another local creates a second array.
- Removing an element can transfer its payload to the result. The collection's own backing follows its documented rule. See the [collection index](../which-bytes-count/collections/README.md).
- Dropping an owner, explicitly or at scope exit, releases the allocations it still owns exclusively. A moved-out child follows its new owner.
- On an early return or loop exit, account for the cleanup on that path. A consuming iterator retains its backing until it is dropped, even after yielding the last item.
