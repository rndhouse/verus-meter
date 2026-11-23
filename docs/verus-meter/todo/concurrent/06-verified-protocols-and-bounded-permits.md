# 06. Verified protocols and bounded permits

Dependencies: 01–05. All code paths below are relative to the repository root.

## Goal

Connect existing Verus synchronization proofs and user-defined implementations to
the same memory analysis as standard mutex contracts. Deliver the concrete
semaphore/permit support selected in 01. Custom protocols are required core
functionality, not a later extension or a user-accessible trust escape hatch.

## Work

- [ ] Implement the verification interface designed in 01–02. Connect executable
  synchronization transitions to proved invariants and owned protocol evidence.
  Establish initialization and preservation, including interference between workers.
- [ ] Make contract acceptance depend on verified behavior. Merely declaring a
  protocol, naming a function `lock`, or writing an unrelated abstract state
  machine must not establish exclusion for executable allocations.
- [ ] Reuse applicable vstd invariant, atomic and tokenized state-machine facilities.
  Maintain namespace/atomicity rules and the supported memory orderings from 01.
  Do not hold atomic invariants open over allocation or blocking calls.
- [ ] Integrate existing verified synchronization, including the selected RwLock
  surface, with its actual release semantics. Avoid re-proving library guarantees
  already available; identify any genuinely missing exported proof facts.
- [ ] Implement the selected bounded-permit protocol/API. Preserve permit instance
  and capacity relationships through acquire, move, borrow and release. Model
  every admitted capacity mutation; unsupported mutations must reject explicitly.
- [ ] Connect both exclusive and bounded-holder facts to compiler-derived per-holder
  footprints. Count failed attempts, waiting storage, retained buffers and repeated
  acquisitions correctly. A permit released early cannot keep covering its buffer.
- [ ] Allow developer-supplied invariants and arithmetic lemmas through the normal
  Verus proof path, without manual byte credits or allocation counters.

## Verified library and custom protocol proofs

Feature commit `69cf54489` implements the fixed-capacity vstd semaphore.
A successful compare-exchange takes a linear unit token. Explicit release
consumes it and increments the atomic word. The executable test checks that
dropping a permit leaves the slot occupied, including across a worker handoff.
The public holder proof covers any finite collection of owned witnesses from
the same instance. The existing RwLock proves writer uniqueness and writer/reader
incompatibility with its existing tokens.

The source regressions verify a custom boolean CAS protocol, reject issuing its
witness on failure, reject an unprovable holder count, and check permit identity
after a conditional return from a worker helper. These functional proofs passed
with the full vstd verifier. The compiler still needs to attach them to live
allocation footprints, preserve their bindings through calls and worker visits,
and account for executable protocol bodies. Keep the integration criteria open
until memory regressions exercise those paths.

Feature commit `6af4fb2ba` connects the underlying permissioned atomics to
source byte accounting. The executable CAS regression needs 20 bytes with a
boolean success test and 75 bytes when the failure branch has a 64-byte local.
Each test rejects a budget one byte smaller. The checked counter helpers and
the executable bodies inside invariant blocks still need source accounting
before their footprints can be used by callers.

## Completion criteria

A user-defined protocol implemented with the supported atomics exposes proved
synchronization effects consumed by the existing lifetime analysis. The selected
semaphore supports a symbolic capacity and justified holder-count constraint.
Standard primitives and verified protocols share composition interfaces; neither
requires a parallel hand-maintained memory model. Allocation sizes and lifetimes
continue to come from executable code.

## Validation

Test a custom exclusive protocol and a bounded-permit protocol with actual
executable acquire/release operations. Break the exclusive protocol, remove its
successful-acquisition check, release a permit early, use the wrong instance and
attempt to fabricate extra permits; the relevant proofs must fail. Test repeated
acquisition and all selected capacity effects. Pass a verified witness through a
helper in a worker, return it on one path and release it on another. Check the
actual instance and capacity on both paths. Test the existing RwLock's explicit
release behavior independently of standard guard drop. Establish custom protocol
properties in the acceptance tests through ordinary verification without `assume`.

Run the README memory checks plus relevant atomic/invariant/mode regressions.
End-to-end symbolic memory bounds using these proofs are required in 07–08.

## Decisions from TODO 01

Implement the verification obligations in `docs/verus-meter/concurrent-model.md`:

- [ ] Check initialization, executable transition refinement, invariant-preserved
  holder multiset bounds, witness encapsulation and interference stability. Local
  postconditions or a disconnected abstract state machine are insufficient.
- [x] Deliver reusable verified `vstd::resource::semaphore::Semaphore` and unit
  `Permit` with new/acquire/try_acquire/explicit release, immutable symbolic capacity
  and occupied capacity for discarded unreleased witnesses. Use existing SC
  PAtomicBool/PAtomicUsize facilities; no async runtime dependency is required.
- [ ] Support the selected vstd RwLock read/write APIs with explicit release and
  persistent payload ownership. Readers do not gain writer-style exclusion.
- [ ] Account for executable fields/locals of verified bodies. Only reviewed opaque
  primitive contracts use the source abstraction table; custom code has no blanket
  zero-workspace exemption.

## Starting points

- `source/vstd/invariant.rs`
- `source/vstd/atomic_ghost.rs`
- `source/vstd/rwlock.rs`
- `source/vir/src/modes.rs`
- `examples/atomic_increment.rs`
- `source/rust_verify_test/tests/atomic_lib.rs`
- `source/rust_verify_test/tests/open_invariant.rs`
