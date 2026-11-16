# 02. Synchronization contracts and identities

Dependencies: 01. All code paths below are relative to the repository root.

## Goal

Implement the common synchronization representation and trusted standard-primitive
integration. The representation must already accommodate verified custom protocols;
TODO 06 supplies that verification integration and concrete bounded permits.

## Work

- [x] Represent stable synchronization-instance identities, individual acquisition
  lifetimes, guards/permits, acquisition outcomes and release/capacity effects in
  the memory analysis. Preserve them through local aliases and moves.
- [x] Recognize supported standard mutex operations using resolved compiler/library
  definitions. Type aliases and imports work; same-named unrelated functions gain
  no trusted semantics. Keep frontend changes thin and model logic focused.
- [x] Encode the reviewed standard Mutex contract without re-proving its OS
  implementation. Record assumptions and the supported toolchain/library surface.
  A contract for exclusion must not grant zero memory cost to library work.
- [x] Model actual explicit and implicit guard destruction in execution order.
  Last use is not release. Follow supported result paths: non-acquiring failure
  grants no guard, while a poison error can contain one. Handle or reject paths
  according to 01; poisoning cannot establish a user's invariant.
- [x] Preserve guard ownership, borrow and thread-transfer constraints from Rust
  and Verus. A shared view of a guard does not produce a fresh acquisition.
- [x] Define the registration/checking boundary for verified contracts so custom
  implementations can use the same events without name-based trust. Reserve no
  unchecked user operation that fabricates acquisition or capacity facts.
- [x] Add contract/event tests and diagnostics for unmodeled operations. Unsupported
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

## Decisions from TODO 01

Implement the synchronization and graph interfaces specified in
`docs/verus-meter/concurrent-model.md`. In addition to the work above:

- [x] Implement the selected standard Mutex operations and distinguish acquiring
  poison outcomes from non-acquiring failures; enforce the panic-free domain and
  reject unsupported recovery. Preserve compiler-derived implicit drop order.
- [x] Add the specified opaque source layouts, primitive Result shapes, behavioral
  contracts and model version. Share static/runtime size policy; no library call
  becomes memory-free merely because its exclusion contract is trusted.
- [x] Define the synchronization-effect declaration schema with instance/witness
  projections and explicit verification obligations. No custom declaration may
  confer facts before TODO 06 validates its certificate.

## Integration boundary

The compiler supplies `synchronization::CompilerEvidence` to the memory pass.
Its `flow::Graph` preserves drop-elaborated compiler control flow, source binding
identities/modes, temporary and field moves, borrowed views, result discrimination,
helper boundaries and actual destructor execution. Acquisition outcomes include
compiler-derived guard projections and tag tests: poisoned results still own a
guard; WouldBlock does not. Constructor/acquisition points name static sites;
consumers must freshen their dynamic visits. Different input binders do not
establish different lock instances.

The graph is a symbolic transport representation, not another byte-accounting
interpreter. TODOs 03–04 resolve its relationships alongside actual live storage;
05 substitutes checked helper effects. Unsupported operations/projections and
missing or ambiguous source bindings cannot supply exclusion evidence. Tracked
bindings remain available for checked protocol witnesses but cannot become
runtime storage or native mutex facts simply by appearing in lifetime-check MIR.

Native functional specifications expose construction/acquire/borrow APIs and
try-lock variants without assuming success, progress or a payload invariant.
Exceptional edges remain explicit; the panic-free memory domain cannot be
bypassed by assuming an acquisition succeeded or disabling lifetime checks.
Resource-contracted runtime synchronization remains rejected until allocation
coverage and concurrent bound checking are implemented. TODO 06 owns custom
certificate verification; an unchecked declaration cannot produce a trusted
contract. Completing this task does not enable concurrent peak proofs.

## Starting points

- `source/rust_verify/src/resource/memory/intrinsics.rs`
- `source/rust_verify/src/resource/memory/cleanup.rs`
- `source/vir/src/resource/memory/synchronization/flow.rs`
- `source/rust_verify/src/fn_call_to_vir.rs`
- `source/vir/src/ast.rs`
- `source/vir/src/resource/memory/execution.rs`
- `source/vstd/std_specs/smart_ptrs.rs`
- `source/vstd/rwlock.rs` (explicit release differs from standard MutexGuard drop)
