# 04. Allocation and synchronization lifetimes

Dependencies: 01–03, including completion of 03.1–03.4. All code paths below are
relative to the repository root.

## Goal

Automatically connect real allocation lifetimes to synchronization states. The
facts must be derived from executable operations, not manually supplied memory
counters. Consume the checked worker effects and identity binders introduced in
03.2–03.3. TODO 05 extends these relationships through general helper summaries.

## Integration boundary

Join the existing allocation/ownership effects with 02's synchronization effects
on the same executable control flow, using the summary foundation from 03.2.
Retain source branches, ordering and intermediate storage; a scalar worker peak
cannot recover containment. Compiler cleanup facts are valid source-semantic
evidence, without requiring a particular generated closure-wrapper shape or
counting compiler-generated implementation storage.

This task owns local lifetime attribution and its proof obligations. 03 already
connects actual worker bodies, completion/join and symbolic ownership populations;
05 owns general interprocedural composition of the relationships added here.

## Completion evidence

Implemented on `feature/concurrent-symbolic-analysis` through `61c7eac2d`. The checked effects carry the same source observations used for byte obligations. Fixed allocations keep their source constructor and worker or loop visit through transfers. Runtime collections retain their existing element-forest descriptors.

- `124573f58` preserves the owned payload of a local mutex. The nested vector example verifies at 113 bytes, rejects 112, and verifies zero after drop.
- `05a87684b`, `aaa964dae`, and `1ee98ed5f` connect acquisition and release to the actual mutex instance, including captured aliases, poisoning, and non-acquiring try-lock outcomes. Dropping a 64-byte buffer before unlock leaves 10 modeled bytes at release. Reversing those operations leaves 82.
- `004620490` and `56847f669` account for the declaration order of struct fields and all permitted closure capture cleanup orders. Conditional returns, nested sections and repeated acquisitions retain their own observations.
- `61c7eac2d` checks guarded replacement, vector growth beyond a reservation, and removal of an owned element. Dropping the guard and mutex leaves 73 bytes in the popped option. A claim of 72 fails. A separate handoff test checks that a spawned worker owes all 72 bytes of a captured box in either unlock/join order. A claim of 71 fails.

The implementation passed all 1,175 resource memory tests, including 33 synchronization cases, plus 88 VIR memory unit tests, 47 resource examples and 606 upstream regressions. General helper substitution, guard returns and updates to an owning payload shared across workers belong to 05. Verification of a total concurrent bound using these local relationships belongs to 07.

## Work

- [x] Attach synchronization conditions to simultaneous allocation/value footprints
  while preserving sizes, explicit reservations and input ownership.
  Keep the complete footprint of an acquired interval, not one allowance per object.
- [x] Establish contained lifetimes for allocations created after acquisition and
  released before unlock. Include supported branches, loops, explicit drops,
  implicit scope exits, replacements and early exits.
- [x] Cover every permitted order of implicit closure-capture destruction; Rust
  leaves this order unspecified. Neither capture indices nor one compiler-selected
  cleanup sequence can establish exclusion. Retain ordering where source rules
  define it, including explicit drops and struct-field destruction.
- [x] Track allocations created before locking or surviving release as independent
  live storage. Moving a buffer to a result, collection or shared owner preserves
  its charge and invalidates any unjustified containment claim.
- [x] Distinguish each acquisition lifetime. Reacquisition cannot repair the gap
  during which escaped storage was alive without the guard.
- [x] Export these relationships through the existing checked effect interface,
  preserving allocation, instance, acquisition and worker-occurrence identities.
  A release changes the conditions on surviving storage, not its ownership or byte
  charge. Do not assume another worker stops while local effects are analyzed.
- [x] Preserve each live payload's charge across ownership transfers and past its
  last read. Track a collection's slots separately from payloads its elements own. For a
  guarded vector, a push uses a reserved slot or adds one occupied slot. A pop
  reduces the slot charge down to the explicit reservation. If it returns a box,
  track the payload until its modeled lifetime ends, including across unlock.
- [x] Charge both buffers when source code constructs a replacement while the old
  buffer is live. A resize internal to `Vec::push` adds no intermediate charge.
  Apply the [vector rules](../../../accounting/which-bytes-count/collections/vectors.md)
  at the call.
- [x] Account collectively for several buffers and any supported concurrent work
  associated with one guard. Borrowing or sharing a guard must not duplicate its
  per-holder allowance.
- [x] Generate the necessary coverage/lifetime proof obligations and protect model
  state from user writes. Integrate with Verus proof contexts without keeping an
  atomic invariant open around arbitrary allocations.
- [x] Diagnose invalid lifetime relationships at the relevant allocation, transfer
  or release. Legal escaping allocations must still work with a sufficient bound
  once composition is integrated; do not forbid escape to manufacture precision.

## Completion criteria

Every supported live allocation remains covered at every transition. The checker
can distinguish contained scratch from retained storage using executable evidence.
Identical memory operations with different lock/drop ordering produce different
relationships, and editing executable allocations changes generated obligations.
No user-maintained allocation counter can bypass this accounting.
The resulting conditions attach to 03's checked worker effects and can be
instantiated by 05 without reconstructing lifetimes from aggregate byte bounds.

## Validation

Test contained scratch, allocation before locking, early release, escaping owners,
conditional drop, repeated acquisition, multiple buffers, and guard aliases.
Check explicit replacement overlap, a push beyond the reservation, and a popped
payload that survives unlock. Include mutations adding a real allocation with no proof-code
change. Check local relationships/obligations now; TODOs 07–08 must test their
resulting total bounds. Run the README's memory checks and affected drop/ownership
regressions, preserving existing sequential lifetime tests.

## Decisions from TODO 01

Use `docs/verus-meter/concurrent-model.md` for graph and coverage semantics:

- [x] Maintain disjoint byte attribution with additional guard conditions retained
  as constraints. Release must reclassify surviving regions, not delete them.
- [x] Cover every supported cleanup edge, protected-payload replacement and
  source-level construction transient. Detect missing compiler drop information rather than
  substituting last-use estimates.
- [x] Translate every transition-review case assigned to local lifetime accounting
  into regression obligations; preserve acquisition-family freshness in loops.

## Starting points

- `source/vir/src/resource/memory/accounting.rs`
- `source/vir/src/resource/memory/lifetime.rs`
- `source/vir/src/resource/memory/allocations.rs`
- `source/vir/src/resource/memory/control.rs`
- `source/vir/src/resource/memory/symbolic.rs`
- `source/vir/src/resource/memory/summary.rs`
- `source/vir/src/resource/memory/synchronization/flow.rs`
- `source/vir/src/resource/memory/workers/body.rs`
- `source/rust_verify_test/tests/resource/memory/lifetimes.rs`
- `source/rust_verify_test/tests/resource/memory/owned_replacement.rs`
