# Which bytes count?

## Principles

- Count storage the program creates or explicitly reserves. This includes inline values, owning handles, and separately allocated payloads.
- Reading or borrowing an existing value adds no storage by itself. Storing a copy or a reference occupies space in its destination.
- Count each allocation once across its owners and borrowers. A handle stored inside a collection already occupies its element slot.
- A supported library operation contributes its documented source-level effects. Its private representation, scratch space, and allocation strategy add no further charges.
- Executable user code follows the same rules inside a helper or a supported callback. An operation whose storage effects the verifier cannot account for requires an unsupported-operation diagnostic.

## What is a model byte?

- The current model assumes a 64-bit target. An integer uses its modeled width, an array contains its elements inline, and a supported struct contains the sum of its fields.
- Compiler-generated bookkeeping, ABI padding, allocator metadata, spare capacity chosen by the allocator or library, and erased proof state are outside the budget.
- A reference held in a struct field costs the modeled size of that reference. Following it to read a field adds no copy of the pointee.

## How does this apply to iteration?

- In a borrowed loop, accessing the current item adds no charge for the implicit iterator, its bookkeeping, or the reference supplied just to visit the item.
- Storing the item or its reference in an output collection charges the destination slot. A consuming loop can also keep the input's backing and unvisited payloads live.
- The verifier currently charges hidden iteration storage. The [audit](../todo/audit-and-correct-source-accounting.md) tracks the correction.
