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
acquisition and all selected capacity effects. Test the existing RwLock's explicit
release behavior independently of standard guard drop. Use ordinary verification,
not `assume`, to establish custom protocol properties in acceptance tests.

Run the README memory checks plus relevant atomic/invariant/mode regressions.
End-to-end symbolic memory bounds using these proofs are required in 07–08.

## Starting points

- `source/vstd/invariant.rs`
- `source/vstd/atomic_ghost.rs`
- `source/vstd/rwlock.rs`
- `source/vir/src/modes.rs`
- `examples/atomic_increment.rs`
- `source/rust_verify_test/tests/atomic_lib.rs`
- `source/rust_verify_test/tests/open_invariant.rs`
