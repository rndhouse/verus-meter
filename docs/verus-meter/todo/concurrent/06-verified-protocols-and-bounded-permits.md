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
- [x] Implement the selected bounded-permit protocol/API. Preserve permit instance
  and capacity relationships through acquire, move, borrow and release. Model
  every admitted capacity mutation; unsupported mutations must reject explicitly.
  - [x] Meter calls to an existing vstd semaphore's `try_acquire` and `acquire`
    methods and to `Permit::release` using their verified executable workspaces.
  - [x] Meter `Semaphore::new(k)`, including its generic atomic constructor.
- [ ] Connect both exclusive and bounded-holder facts to compiler-derived per-holder
  footprints. Count failed attempts, waiting storage, retained buffers and repeated
  acquisitions correctly. A permit released early cannot keep covering its buffer.
  - [x] For a concrete custom guard with a local holder proof, record which
    executable allocations are live while the guard is intact. Preserve its
    identity through a direct whole move, a checked helper call and an owned
    worker capture passed to a checked helper.
  - [x] Preserve the actual input witness through direct and conditional helper
    returns, including a permit moved into a worker. Check every successful
    return path before attributing the result to a particular input.
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
with the full vstd verifier. To apply a population proof across workers, the
memory analysis must identify the instance that issued each live guard.

Feature commit `6af4fb2ba` connects the underlying permissioned atomics to
source byte accounting. The executable CAS regression needs 20 bytes with a
boolean success test and 75 bytes when the failure branch has a 64-byte local.
Each test rejects a budget one byte smaller. Feature commit `80b2504bd`
measures the checked counter helpers from their executable vstd bodies and
publishes their workspace after full verification and lifetime checking. A
checked-add caller needs 56 bytes. A vstd build with verification disabled
cannot supply that footprint. An open atomic invariant counts its executable
local and still has to restore its invariant.

Feature commits `ef824af83` and `5b0e16208` require successful erased Rust
checking before publishing a helper workspace and account for the custom CAS
guard’s executable methods. Its acquisition attempt needs 30 bytes and its
explicit release needs 33. Both reject one byte less. Moving an erased token
out of a guard can end its eligibility as a whole proof witness while its
reference slot remains live.

Feature commits `be0b04007` and `22e26be27` track which allocations are live
with a particular intact guard. The regression distinguishes two 64-byte
boxes in one call by freeing one before release and retaining the other. It checks
which helper argument owns the guard, distinguishes an owned worker capture from
a shared borrow, and checks both whole moves and the last statement before
implicit cleanup. A helper reserving `n` bytes, dropping its vector and then releasing
the guard verifies at 41 bytes for `n == 0` and `n + 40` for `0 < n <= 500`.
Reducing either allowance by one byte fails.

Feature commit `93c4099e7` follows an existing guard returned directly or in
`Some`. A helper may release it and return `None` on another path. Swapping
two same-typed arguments changes which input covers the buffer and fails the
original issuer assertion. If an early return and the tail can return different
guards, the result has its own local lifetime with no single input attribution.

Feature commit `d8abf4812` meters the imported vstd permit. The test callers
need 81 bytes for `try_acquire`, 98 for `acquire` and 72 for `release`. Each
rejects one byte less. A worker can move a permit into a helper and receive it
back on the successful path. Separate vstd builds with verification or lifetime
checking disabled supplied neither a holder proof nor an acquisition workspace.

Feature commit `8defaa5d3` connects independently acquired witnesses to the
symbolic capacity and instance projections of the actual receiver. A custom
CAS acquisition and the vstd semaphore use ordinary verified postconditions.
Two workers acquiring through cloned strong handles report the same backing
for their 51-byte and 52-byte buffers. Substituting a second semaphore with the
same capacity reports distinct backings. A conditional issuer assertion cannot
supply this relation. TODO 07 consumes these facts for the combined peak.

Feature commit `c894af372` measures semaphore construction, including its
generic atomic wrapper. A caller verifies the returned capacity equals the
symbolic input and needs 40 bytes. A 39-byte bound fails.

Feature commit `660d3973c` measures the seven public RwLock methods, including
their verified permissioned-cell helpers, at the concrete payload width. The
tests compare simultaneous reader/reader and writer/reader roles on one lock
and on two distinct locks. For inline payloads, each operation has a passing
byte bound and a failing bound one byte smaller. Persistent ownership of a
separately allocated payload remains to be checked.

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
