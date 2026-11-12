# 5. Borrowed collections and incoming ownership

Builds on tasks [1](01-compose-iteration-operations.md) through
[4](04-indexed-traversal.md).

## Goal

Apply the supported loop transformations to collections supplied by callers,
whether moved into the function or borrowed, and preserve that support through
helper delegation.

## Supported boundary

Incoming owned and borrowed collections use the same checked loop operations,
including repeated extraction, indexed updates and replacement, and nested
runtime paths. Calls preserve the caller's remainder and transferred results
independently. Direct and delegated operations share the ownership template;
local charge views remain separate from complete caller allocation forests.

A logical source supplies missing incoming geometry through zero-byte descriptors.
A fresh fixed wrapper does not turn its incoming children into fully charged
storage. Template instantiation permits exact-capacity inference only with
complete byte charges. Known-zero output charges are proved before adoption;
loops retain zero-charge facts only through checked inductive invariants.

Original regions compose at argument, intermediate-peak, and output paths. Indexed
loans update their enclosing persistent region; allocations introduced by the
callee never enter those original-only expressions. Structural mutations remain
visible even when their local byte charge is zero. Derived input lifetimes also
require precise templates behind fixed and unit results.

Ordered loop outputs expose requested inverse removal views for later caller
extraction. Ordinary branches, optional-match protection, and memory-section
restrictions remain in force. Missing geometry, unsupported ownership shapes,
and unsupported control or scalar dependencies reject. Broader progress/count
proofs remain in [task 6](06-iteration-counts-and-state.md), and other loop
forms remain in [task 7](../07-loop-forms-and-exits.md).

## Work

- [x] Carry precise caller-supplied ownership descriptors through supported loop
  operations without treating zero local charge as an empty incoming allocation.
- [x] Support repeated extraction and indexed updates through borrowed inputs,
  preserving the caller's remainder and any transferred results.
- [x] Compose incoming ownership through helper calls using the same operation
  model as direct execution.
- [x] Keep original allocation lifetimes separate from allocations created by the
  callee and update caller ownership exactly once after the call.
- [x] Replace protection guards only where a checked lifetime transition now
  justifies the operation. Preserve unrelated branch and memory-section limits.

## Completion criteria

Tests compare direct and delegated owned/borrowed operations, including empty
collections, partial traversal, nested children, and caller use after calls.
Exact budgets and one-byte-short checks distinguish surviving and extracted
allocations. Intermediate-peak checks keep original storage live across delegated
calls. Capacity checks reject fictitious spare room inferred from zero local
bytes, including through fresh fixed wrappers. No copied parent charge or
aggregate ownership fallback is introduced.

## Starting points

- [Input regions](../../../../../source/vir/src/resource/memory/provenance.rs)
- [Call provenance](../../../../../source/vir/src/resource/memory/transfer/origins.rs)
- [Call geometry](../../../../../source/vir/src/resource/memory/metadata/geometry.rs)
- [Call composition](../../../../../source/vir/src/resource/memory/transfer/calls.rs)
- [Incoming loop regressions](../../../../../source/rust_verify_test/tests/resource/memory/incoming_loops.rs)
