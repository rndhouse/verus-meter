# Memory contracts

Verus Meter verifies upper bounds on peak source-level memory for supported Rust programs. The [accounting policy](verus-meter/accounting/README.md) defines model bytes, their lifetimes, and how they combine.

## How do I read a contract?

- `resources peak(memory) <= bound` requires every allowed execution of the function or section to fit the bound. Ordinary Verus obligations, including bounds and overflow checks, still apply.
- In the [nested sections example](../examples/resource/memory/contracts/sections.rs), the function keeps an array, a section makes a copy, and an inner section makes scratch space. All three arrays are live at the peak.
- `assert(current(memory) <= bound)` checks what is live now. `assert(peak(memory) <= bound)` checks the peak so far. Both refer to the nearest budgeted section or function and currently require fixed bounds.

For the sequentially consistent vstd permissioned atomics, a boolean location occupies one model byte and a `usize` location occupies eight. A compare-exchange charges its executable arguments and tagged result. Scratch storage on a failed attempt counts through its ordinary source lifetime. A tracked permission occupies zero bytes. The checked add/subtract methods include the workspace of their verified vstd bodies. Opening an atomic invariant preserves the cost of its executable statements and the ordinary Verus obligation to restore the invariant. An atomic-backed guard can carry a reference to its issuing instance alongside erased protocol evidence. Copying that reference into a local during release creates a new reference slot. A raw atomic operation by itself establishes no protected allocation lifetime.

A metered function taking a vstd `Semaphore` reference or an owned `Permit` can call `try_acquire`, `acquire` and `release`. The model derives the eight-byte layouts of the semaphore and permit from their executable fields. The library exports the measured workspaces and the permit’s holder proof after verification and lifetime checking. An unsuccessful attempt supplies no permit. An unreleased permit continues occupying its slot even if the program drops the value. A metered caller can also create the semaphore at a symbolic capacity. Its constructor includes the measured workspace of the generic atomic wrapper, whose type parameters describe erased proof state. [Executable semaphore contracts](../source/rust_verify_test/tests/atomic_lib/semaphore.verus.rs)

The verified vstd `RwLock<V, Pred>` has an inline payload slot, one boolean atomic and one word-sized atomic. Each read or write handle contains one reference. The analyzer measures construction, both acquisitions, shared borrow, explicit release and `into_inner` from their executable vstd bodies. It instantiates the verified bodies at the actual payload width, including work in the permissioned cell wrappers. The opaque initialized cell and Rust’s `MaybeUninit` each store one payload slot. The primitive reference operations on those slots add their executable arguments and results. The writer receives the value and a distinct handle. A reader’s role excludes a writer on the same instance and allows another reader. Discarding a handle leaves the protocol occupied. [Executable RwLock contracts](../source/rust_verify_test/tests/atomic_lib/rwlock.verus.rs)

For an owned payload, the lock retains the allocation tree installed by construction. Reading borrows that tree. A successful writer takes it out. Explicit write release puts the supplied value into the issuing cell, so a displaced buffer can outlive release and overlap a new allocation. Moving the lock through an owning helper or into a worker preserves its payload. `into_inner` transfers the current tree to the caller. The underlying vstd cell uses `ManuallyDrop`, so the analysis rejects ordinary destruction of a populated lock with separately owned storage. [Owned-buffer examples](../source/rust_verify_test/tests/atomic_lib/rwlock_owned.verus.rs)

For a fixed shared lock, a worker that acquires a writer receives the allocation tree available at that acquisition. Explicit release publishes the replacement to the same lock. Supported joins recover the last possible published tree. A reader may observe the current value without importing a second charge for it. Consuming a heap-owning writer in a helper requires a checked outgoing cell version. If the call cannot identify that version, verification reports unsupported. [Shared replacement and recovery](../source/rust_verify_test/tests/atomic_lib/rwlock_shared.verus.rs)

For a concrete custom guard with a local `BoundedHolder` proof body, the memory trace can show which allocations are live while the guard is intact. This covers owned inputs, initialized immutable locals and a guard bound on the successful arm of an acquisition. Moving the guard into a checked helper associates the helper’s observations with the actual argument. A worker can supply that argument from a guard moved into its closure. A buffer that survives release stays charged, even when the tracked token occupies zero bytes. A direct move to another immutable name preserves the same witness through the move. A checked helper can return the guard directly or inside `Some`, optionally releasing it on a `None` path. The successful result keeps the identity of the caller’s argument when every returning path that supplies a guard agrees on that argument. If a helper can return either of two inputs, its result still covers local storage while held. A custom issuer can implement `ProtocolInstance` and `BoundedInstance` and prove `issued(result, issuer)` or `issued_on_success(result, issuer)` in a standalone postcondition. These ordinary Verus predicates relate the returned witness’s instance and capacity to immutable projections of the same executable receiver. The analyzer substitutes actual issuer arguments at helper calls and follows captured receivers and clones of a fixed Arc backing into independent workers. Equal capacities alone supply no instance relation.

In the custom guard regression, a helper reserves `n` bytes in a vector, drops it and then releases its guard. For `n <= 500`, the verified peak is at most 41 bytes when `n == 0` and `n + 40` otherwise. Reducing either allowance by one byte fails verification. [Guard regressions](../source/rust_verify_test/tests/atomic_lib/holders.rs) · [Custom lock and proof](../examples/resource/memory/concurrent/custom_mutex/protocol.rs)

## How do I express a bound?

- `value_size(T)` measures inline storage. `ref_size(&T)` measures a reference. Both also accept binding names. `return_size(f)` measures the inline size of the declared result.
- `peak(f(args))` gives the declared allowance for those arguments. `peak(f)` gives the maximum declared allowance.
- Function budgets can use immutable scalar inputs, arithmetic, conditionals, and supported local spec helpers. Section budgets can also use executable locals and named slice or vector lengths. Budget arithmetic must fit in `u64`.
- A function marked `#[queryable_peak_memory]` can expose its allowance at runtime. Its caller still establishes the function's preconditions. [Runtime queries](../source/verus-meter/runtime/README.md)

## What can I verify today?

- Supported cases include concrete values, arrays, structs, options, boxes, vectors, boxed slices, selected loops, and safe nongeneric helpers in the same crate with an acyclic call graph. Support depends on the operation and the ownership facts available. [Executable examples](../examples/resource/memory/README.md)
- Constructing a local standard mutex charges its inline state and payload. Moving it transfers the payload's existing allocations, and dropping it releases the allocations it still owns.
- A blocking lock on a known local mutex or a captured strong alias retains the caller’s storage while it waits. On normal return both success and poisoning carry the guard. Dropping that owner ends the acquisition and leaves any surviving buffer charged.
- For a native `try_lock`, the success and poison arms own an acquisition. The `WouldBlock` arm retains the caller’s storage without acquiring the mutex. The verifier checks the actual match arm or the normal precondition on `unwrap`.
- Checked helpers preserve the mutex instance and the acquisition owned by a guard. A helper can borrow, consume or return a guard. Its waits and releases include storage still held by the caller. A worker can call a helper that returns the lock result for its captured shared mutex. The first access through the resulting guard binds the actual protected contents. A helper taking that guard can replace the contents and release the guard. A worker can also pass the shared mutex to a helper that locks it, appends to its vector and unlocks before returning. Each append uses the vector that worker actually acquires, including elements an earlier worker inserted.
- Strong aliases refer to one protected payload. For a bounded set of single-visit worker acquisitions, the verifier checks the published contents and what each guard leaves at unlock. For a lock in a worker loop, a proposed set of contents must include the initial state and cover every possible release on every visit. The next holder can receive any contents a preceding holder could leave on that mutex. With one push and one pop on an initially empty vector, the pop can receive the pushed box or find the vector empty. Both possibilities count regardless of join order.
- Guarded vector operations use the ordinary source-level rules for occupied slots, explicit reservations and owned elements. A popped box stays charged to its new owner. If the verifier cannot describe every possible update or the number of histories exceeds its search limit, it keeps the incoming payload unrestricted. A fixed worker can return a removed element through a direct join. The completion record retains its owned allocations until the caller receives them. After all writers join, the remaining vector and the returned value use the same possible lock order. Dropping or uniquely extracting the mutex therefore preserves the ownership of each surviving allocation. Fixed-worker totals include retained results and shared payloads for which the analysis can link every acquisition and release.
- Spawning while holding a mutex transfers the captured storage to the worker. The spawning thread retains its own guard until release. [Concurrent specification](verus-meter/concurrent-model.md)

For fixed, directly joined workers returning unit, a function can verify a total peak
with symbolic scratch sizes taken from immutable scalar parameters. The caller pays
for the shared backing once and for each outstanding completion tag. Two workers can
each reserve and free a vector under the same native mutex using one vector's worth of
scratch in the bound. A buffer allocated before locking or kept after unlocking can
overlap another worker's buffer. The checks also include handle slots, captures and
live caller storage. To use a symbolic vector reservation in the combined peak,
the verifier checks that the reservation still covers the vector's charge at that
point. [Executable cases](../source/rust_verify_test/tests/resource/memory/fixed_workers.rs)

Four workers can share one buffer's worth of scratch when the same mutex guard
stays live across the helper that allocates and frees it.
[Mutex lifetimes](../examples/resource/memory/concurrent/mutex_lifetimes.rs)

When each worker pushes a 256-byte buffer into an initially empty shared vector,
the caller can still hold 1,177 bytes after all joins. The shared cell and handle
occupy 57 bytes, and each inner vector contributes a 24-byte slot and its
256-byte reservation. [Retained buffers](../examples/resource/memory/concurrent/retained_buffers.rs)

A fixed-budget section can publish workers if every descendant joins before each
reachable section exit. The caller pays the section allowance alongside its own live
storage. A current checkpoint includes the workers still covered at that point.
A peak checkpoint also includes earlier reachable worker phases, including prior
loop iterations. In a worker, a current checkpoint covers its own subtree and the
incoming shared backing it can still observe. A peak checkpoint needs a budgeted
section in that worker to establish where the history begins.
[Executable section and checkpoint cases](../source/rust_verify_test/tests/resource/memory/concurrent_scopes.rs)

A counted loop can publish workers from one spawn site into handle vectors and
join them in a drain loop. The verifier counts actual publications and joins,
then proves how many workers the vectors represent at each loop boundary.
For up to `n` workers reserving `b` bytes each, unrestricted scratch can reach
`n * b`. If each buffer is allocated and freed under the same mutex constructed
outside the loop, scratch is zero for no workers and at most `b` otherwise.
Joining each worker before the next spawn also permits reuse. The total includes
caller storage, handles, captures, shared backing and any inline scalar results
awaiting collection. Ordinary loop invariants and arithmetic proofs can establish
collection lengths and the range of a symbolic product. [Counted worker regressions](../source/rust_verify_test/tests/resource/memory/counted_workers.rs)

With one shared semaphore of immutable capacity `k`, up to `n` workers can
charge `(if n <= k { n } else { k }) * b` for scratch when each successful
permit covers at most `b` live bytes. Two buffers under one permit contribute
their combined size. The total also covers waiting, failed attempts, and
storage surviving release. A checked constructor can expose
`result.holder_limit() == slots` on its whole result. The analysis uses the
actual scalar argument when that result initializes a shared Arc outside the
publishing loop. A custom guard with a verified population theorem and constant
capacity can use the same composition. For a verified RwLock, two readers can
overlap, while a writer excludes another reader or writer on the same instance.
[Symbolic semaphore example](../examples/resource/memory/concurrent/semaphore.rs)

The collected population uses an immutable upper bound from the publishing loop's
condition. Verus checks it at every spawn. At a compound expression that can
spawn or join, the proof may charge that ceiling to cover changes during operand
evaluation. Multiple publishing families in one collection, owned results, general worker
helper calls and scoped concurrent checkpoints still require further composition.
