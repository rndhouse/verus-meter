# Arrays and slices

- **Fixed array.** An `[T; N]` occupies `N * value_size(T)` inline. Copying a copyable array into a second live local charges both arrays.
- **Borrowed slice.** A stored `&[T]` occupies `ref_size(&[T])`. Taking a view of an array or buffer preserves the owner's element storage. Indexing through the view adds no element allocation.
- **Boxed slice.** A `Box<[T]>` has a handle and a separately owned buffer of `len * value_size(T)` bytes. Moving it transfers the buffer and any allocations its elements own.
- **Consuming conversion.** Converting an owned vector into a boxed slice consumes the source and retains its elements. The policy excludes a replacement performed privately by the library. The verifier currently charges old and new buffers together on this operation. See the [audit](../../../todo/remove-excess-memory-charges.md).
