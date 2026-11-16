# 04. Allocation and synchronization lifetimes

Dependencies: 01–03. All code paths below are relative to the repository root.

## Goal

Automatically connect real allocation lifetimes to synchronization states. The
facts must be derived from executable operations, not manually supplied memory
counters. TODO 05 extends these relationships through helper summaries.

## Work

- [ ] Attach synchronization conditions to simultaneous allocation/value footprints
  while preserving the existing accounting of sizes, capacity and input ownership.
  Keep the complete footprint of an acquired interval, not one allowance per object.
- [ ] Establish contained lifetimes for allocations created after acquisition and
  released before unlock. Include supported branches, loops, explicit drops,
  implicit scope exits, replacements and early exits.
- [ ] Track allocations created before locking or surviving release as independent
  live storage. Moving a buffer to a result, collection or shared owner preserves
  its charge and invalidates any unjustified containment claim.
- [ ] Distinguish each acquisition lifetime. Reacquisition cannot repair the gap
  during which escaped storage was alive without the guard.
- [ ] Maintain conservation across ownership transfers and preserve old/new overlap
  during replacement or reallocation. Logical removal and last use are not release.
- [ ] Account collectively for several buffers and any supported concurrent work
  associated with one guard. Borrowing or sharing a guard must not duplicate its
  per-holder allowance.
- [ ] Generate the necessary coverage/lifetime proof obligations and protect model
  state from user writes. Integrate with Verus proof contexts without keeping an
  atomic invariant open around arbitrary allocations.
- [ ] Diagnose invalid lifetime relationships at the relevant allocation, transfer
  or release. Legal escaping allocations must still work with a sufficient bound
  once composition is integrated; do not forbid escape to manufacture precision.

## Completion criteria

Every supported live allocation remains covered at every transition. The checker
can distinguish contained scratch from retained storage using executable evidence.
Identical memory operations with different lock/drop ordering produce different
relationships, and editing executable allocations changes generated obligations.
No user-maintained allocation counter can bypass this accounting.

## Validation

Test contained scratch, allocation before locking, early release, escaping owners,
conditional drop, repeated acquisition, multiple buffers, reallocation overlap
and guard aliases. Include mutations adding a real allocation with no proof-code
change. Check local relationships/obligations now; TODOs 07–08 must test their
resulting total bounds. Run the README's memory checks and affected drop/ownership
regressions, preserving existing sequential lifetime tests.

## Starting points

- `source/vir/src/resource/memory/accounting.rs`
- `source/vir/src/resource/memory/lifetime.rs`
- `source/vir/src/resource/memory/allocations.rs`
- `source/vir/src/resource/memory/control.rs`
- `source/vir/src/resource/memory/symbolic.rs`
- `source/rust_verify_test/tests/resource/memory/lifetimes.rs`
- `source/rust_verify_test/tests/resource/memory/owned_replacement.rs`
