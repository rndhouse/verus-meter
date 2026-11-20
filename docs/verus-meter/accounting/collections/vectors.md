# Vectors

- A vector has an inline handle. Its backing costs `max(explicitly_requested_slots, len) * value_size(T)`. An element's separately owned payload has its own charge.
- **Construction.** `Vec::new()` requests zero slots. `Vec::with_capacity(n)` requests and funds `n` slots even while the vector is empty.
- **Push.** A push that fits the reservation uses a funded slot. Beyond it, each push adds one element slot. Pushing an existing box transfers ownership of its payload.
- **Pop and remove.** Removing an element releases one slot down to the explicit reservation. A returned owning element keeps its payload live.
- **Access and transfer.** Borrowing the vector preserves the backing charge. Moving it to a new owner carries its reservation, occupied slots, and owned children.

Allocator-selected spare capacity and the transient resize inside a push are outside the source budget. The [vector growth example](../../../../examples/resource/memory/vectors/vector_growth.rs) builds one slot per result and shows how a helper's push is charged.
