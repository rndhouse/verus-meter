# 02. Synchronization contracts and identities

Dependencies: 01. All code paths below are relative to the repository root.

## Goal

Implement the common synchronization representation and trusted standard-primitive
integration. The representation must already accommodate verified custom protocols;
TODO 06 supplies that verification integration and concrete bounded permits.

## Work

- [ ] Represent stable synchronization-instance identities, individual acquisition
  lifetimes, guards/permits, acquisition outcomes and release/capacity effects in
  the memory analysis. Preserve them through local aliases and moves.
- [ ] Recognize supported standard mutex operations using resolved compiler/library
  definitions. Type aliases and imports work; same-named unrelated functions gain
  no trusted semantics. Keep frontend changes thin and model logic focused.
- [ ] Encode the reviewed standard Mutex contract without re-proving its OS
  implementation. Record assumptions and the supported toolchain/library surface.
  A contract for exclusion must not grant zero memory cost to library work.
- [ ] Model actual explicit and implicit guard destruction in execution order.
  Last use is not release. Follow supported result paths: non-acquiring failure
  grants no guard, while a poison error can contain one. Handle or reject paths
  according to 01; poisoning cannot establish a user's invariant.
- [ ] Preserve guard ownership, borrow and thread-transfer constraints from Rust
  and Verus. A shared view of a guard does not produce a fresh acquisition.
- [ ] Define the registration/checking boundary for verified contracts so custom
  implementations can use the same events without name-based trust. Reserve no
  unchecked user operation that fabricates acquisition or capacity facts.
- [ ] Add contract/event tests and diagnostics for unmodeled operations. Unsupported
  concurrent paths must continue to reject until their accounting is implemented.

## Completion criteria

Supported standard mutex operations produce correctly identified acquisition and
release effects through the compiler path. The representation distinguishes two
locks of one type and two acquisitions of one lock. Trusted contracts have an
explicit boundary; arbitrary external functional specifications do not become
memory contracts. The contract interface can express bounded permits and custom
protocol effects without redesigning the basic identity/lifetime representation.

This task does not claim a concurrent peak proof: storage binding, worker
composition and global bound checking are completed in subsequent tasks.

## Validation

Test aliases, unrelated definitions with matching names, guard moves/borrows,
explicit versus implicit release, failed acquisition, supported poison handling,
release/reacquisition and illegal guard transfer. Inspect emitted effects through
compiler tests, not only hand-constructed records. Run affected frontend/mode and
memory checks from the README. If syntax is added, check parser/prettyprinter
round-trips and erasure as well.

## Starting points

- `source/rust_verify/src/resource/memory/intrinsics.rs`
- `source/rust_verify/src/fn_call_to_vir.rs`
- `source/vir/src/ast.rs`
- `source/vir/src/resource/memory/execution.rs`
- `source/vstd/std_specs/smart_ptrs.rs`
- `source/vstd/rwlock.rs` (explicit release differs from standard MutexGuard drop)
