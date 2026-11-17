# Concurrent symbolic memory analysis: core implementation plan

## Goal

Extend Verus Meter to verify symbolic peak-memory bounds for concurrent user
code. Integrate synchronization guarantees already provided by Rust and Verus
with the existing symbolic allocation and lifetime analysis to determine which
allocations can coexist. Reuse those guarantees through trusted or verified
contracts instead of unnecessarily re-proving synchronization implementations.

Users retain control over their synchronization implementations. The analysis
must understand supported standard primitives and connect to Verus proofs about
custom protocols implemented with supported atomics. It must not require users
to replace their synchronization with a prescribed collection of Verus Meter
locks or semaphores.

This document defines one core feature and its completion checklist. The work
areas below are parts of that feature, not separate prototypes or releases.
The [concurrent semantics](../concurrent-model.md) settle the design and supported
operation matrix from TODO 01; implementation checklist items remain open. The
[numbered implementation TODOs](concurrent/README.md) map back to this checklist
and define the workflow for moving completed tasks into `concurrent/complete/`.

Background: [high-level explanation](../high-level-concurrent-symbolic-analysis.md),
[technical assessment](../concurrent-symbolic-analysis.md), and the existing
[memory model](../model.md). This plan incorporates the subsequent clarification
that standard synchronization guarantees and user-defined synchronization proofs
both feed the same memory analysis.

## Required behavior

For `n` workers, each with temporary storage bounded by `b`, the checker should
support both a conservative temporary-storage bound of `n * b` and a tighter
bound derived from synchronization. If a verified protocol guarantees that only
one worker's temporary storage can be alive, that contribution is at most `b`
for nonzero `n`, and zero for `n = 0`.

For example, use the mutual-exclusion contract of Rust's `Mutex` to establish
exclusive guard ownership for the same mutex instance. Automatically establish
from the worker code that its scratch storage is allocated after acquisition and
released before that guard unlocks. Combining these facts gives the `b` scratch
bound. Rust supplies exclusion; Verus Meter must establish the allocation-lifetime
relationship and the resulting byte bound.

The total bound must also include shared objects, local storage, handles,
retained results and other modeled allocations. Synchronization reduces only
the contributions whose lifetimes it actually constrains.

Keep symbolic byte expressions as the primary abstraction. Developers specify
byte bounds and supply invariants and proofs where needed; the compiler derives
allocation events, sizes, transfers, releases and their synchronization-state
relationships. Ordinary uses of a supported mutex should not require users to
restate mutual exclusion or manually annotate each allocation with a counter.
Memory credits and allocation permissions are not the primary user interface.
A manually maintained ghost memory counter is not sufficient evidence for a
memory guarantee.

## Work areas

### 1. Define concurrent accounting and the proof connection

Specify what a concurrent resource contract covers: the coordinator, participating
workers, shared storage and results. Define when storage enters and leaves that
accounting scope, including workers that are waiting or have finished but still
have uncollected results.

Define three connected parts of the analysis:

| Part | Responsibility |
| --- | --- |
| Synchronization semantics | Represent primitive identity, acquisition/release, guard or permit ownership, and exclusion or bounded-holder guarantees. Obtain these from reviewed trusted library contracts or verified implementations. |
| Lifetime relationships | Derive which actual allocations remain live during each synchronization state, including transfers and escapes. Prove any additional relationships that cannot be established structurally. |
| Symbolic composition | Combine simultaneous storage under those relationships to check input-dependent byte bounds. |

Keep the division of responsibility explicit. Rust's type and ownership rules
constrain moves, borrows and legal thread transfers; a supported library contract
supplies its synchronization guarantee. Neither establishes that an independently
allocated buffer is freed before unlock. Verus Meter must check that relationship,
allocation sizes, surviving ownership and all other concurrent storage. `Send`
and `Sync` do not establish mutual exclusion or bound the number of allocations.
The connection must remain valid as other workers execute.

Design this together with function summaries before committing to a representation
that preserves only independent worker peaks. Establish how existing Verus
invariants and tracked proof state support the connection without treating an
entire critical section as one atomic operation.

Integrate this into the existing mode-checked VIR memory pass in
[pipeline.rs](../../../source/rust_verify/src/resource/memory/pipeline.rs).
Extend allocation/lifetime accounting and generated proof obligations rather
than introduce a separate user-maintained model of memory. Fork-specific logic
should remain in focused memory modules with thin frontend integration.

### 2. Track storage across threads

Extend existing allocation identity and ownership accounting across spawning,
execution, completion and joining. Account for captured values, shared roots,
worker-local storage, and results retained after worker completion.

Moves and ownership transfers must preserve one allocation charge. Shared
references must not multiply the payload charge. Storage must remain counted
until a supported release, even when its original owner or worker has finished.

Preserve synchronization-instance identity through aliases, shared handles,
closure captures and thread arguments. Distinct locks with the same type remain
distinct; two handles to one lock refer to the same instance. Track the particular
acquisition/guard lifetime as well, so reacquiring a lock cannot retroactively
cover storage that survived an earlier unlock. Respect the primitive's actual
thread-transfer restrictions; identity propagation must not make an otherwise
illegal guard transfer legal.

Support symbolic worker counts and spawning in loops, with proved bounds on
simultaneous outstanding work. Define the supported shared-ownership operations
and worker lifecycle explicitly; unmodeled operations must fail clearly.

### 3. Integrate synchronization contracts and allocation lifetimes

Give supported primitives a common analysis contract describing their identity,
acquisition outcomes, guard or permit ownership, release events, and exclusion
or capacity rules. There are two sources for these contracts:

- **Trusted standard/library contracts:** encode the documented guarantees of
  identified implementations. For Rust's `Mutex`, reuse mutual exclusion and
  guard-based unlocking without re-verifying the underlying OS lock. Record the
  supported operations, library/toolchain assumptions and trust boundary.
- **Verified contracts:** derive the same facts from existing Verus library proofs
  or user-defined protocols. Custom implementations must prove their advertised
  properties against executable behavior; a user assertion or API name alone
  cannot confer trusted exclusion.

Rust documents access through mutex guards and unlocking on guard destruction in
[Mutex](https://doc.rust-lang.org/std/sync/struct.Mutex.html) and
[MutexGuard](https://doc.rust-lang.org/std/sync/struct.MutexGuard.html). Model
explicit drop and implicit scope-exit drop in their actual order, not last use.
Represent supported acquisition outcomes accurately: a non-acquiring failure
provides no guard, while a poison error may contain one. Poisoning is not proof
that a user invariant holds; handle or explicitly restrict those paths according
to the execution scope.

For semaphores, select concrete supported library operations or verified user
implementations and specify permit identity, capacity, acquisition and release.
Do not assume every semaphore conserves a fixed capacity: permit addition,
splitting, forgetting or other supported mutations need explicit effects.

Follow the compiler-identity recognition pattern in
[intrinsics.rs](../../../source/rust_verify/src/resource/memory/intrinsics.rs):
resolve actual definitions, including aliases, rather than source spellings.
Existing [external specifications](../../../source/vstd/std_specs/smart_ptrs.rs)
provide a precedent for trusted library facts, but their functional specifications
alone are not memory or synchronization contracts. Keep primitive workspace and
storage costs separately modeled; trusting exclusion does not imply zero cost.

Reuse established Verus proofs, including the
[verified RwLock](../../../source/vstd/rwlock.rs), according to their actual
interfaces. Its handles require explicit release, unlike Rust's `MutexGuard`
drop behavior. Preserve Verus atomic-invariant restrictions when integrating
custom protocols; a buffer allocation cannot be justified by pretending an
arbitrary critical section is atomic.

Automatically relate executable allocation lifetimes to these synchronization
states. Handle allocation before acquisition, early unlock, conditional paths,
repeated acquisition, helper calls, and transfer to a result or shared owner.
An escaping allocation remains charged after unlock, either as retained storage
or under another proved relationship. Reject an invalid tight bound, not a legal
ownership transfer merely because it escapes its original critical section.

Exclusion limits independent guard ownership, not automatically the number of
allocations or workers using storage associated with a guard. Bound all storage
attributed to that acquired interval together, including several buffers and any
supported nested work. A borrowed/shared view of a guard must not create a second
independent allowance of `b`.

### 4. Preserve precision across functions and workers

Extend function and worker summaries to describe simultaneous storage,
ownership changes, retained results and the synchronization relationships needed
to compose them. Build on
[FunctionSummary](../../../source/vir/src/resource/memory/summary.rs), which
already carries allocation transformations, input provenance and simultaneous
lifetime profiles. Add synchronization-instance parameters, guard/permit lifetime
relationships and acquisition/release effects rather than exporting only a scalar
worker peak.

Instantiate those identities and effects at each call and spawn. A helper given
two aliases of one lock must preserve their equality; distinct actual locks must
not be merged. Summaries must expose allocations and guards returned to callers,
consumed by helpers, or retained by workers, including storage that survives a
release. Contracts used for tighter composition must be checked or explicitly
trusted, never inferred from a callee's numeric allowance alone.

Helpers may allocate, consume, transfer and return supported owning values.
Moving an operation into a helper should preserve the relationships required for
the same tight bound. Include caller storage that remains live during the call,
and distinguish a spawned worker's lifetime from an ordinary function call.

### 5. Prove combined symbolic bounds

Combine the storage that can coexist under the proved synchronization rules.
Handle input-dependent worker counts and allocation sizes, sequential reuse,
shared allocations, and retained data without double counting. For fixed capacity
`k`, a proved limit of `k` permit holders with at most `b` scratch bytes each gives
`min(n, k) * b`; the per-holder footprint and lifetime relationship must also be
established. Preserve these relationships when sizes and counts are symbolic.

Keep synchronization conditions attached to simultaneous lifetime profiles.
Taking independent maxima first and subtracting alleged savings afterward loses
the correlations needed for sound, tight bounds. Prove the combined bound across
all permitted execution steps, including allocation/reallocation overlap and
storage held while blocked.

Use inductive proofs and summaries rather than enumerating schedules. Permit
user-supplied invariants and arithmetic lemmas when automatic reasoning is
insufficient. Independent peak summation remains a conservative option within
this design, not its only representation.

### 6. Finish integration and validation

Provide diagnostics that distinguish an excessive bound, an unproved
synchronization relationship, and an unsupported operation. Show the contributing
storage, synchronization instance and relevant lifetime boundary where practical.

Test both trusted standard-primitive integration and custom Verus-verified
protocols through the same analysis path. Include positive tests for aliases of
one mutex, helper-contained allocations and symbolic semaphore capacity, plus
negative tests for distinct locks, early guard drop, failed acquisition and
storage that crosses a release/reacquisition boundary. Test supported error/drop
paths or their explicit rejection; do not silently bypass accounting on them.

Complete library integration, regression coverage, executable examples and user
documentation for the agreed supported scope. Preserve existing sequential
memory behavior. Follow the repository's required memory checks and affected
frontend, mode, erasure and function-contract checks when those layers change.

## Core completion checklist

All items are required. A simple mutex example passing does not complete the
feature.

- [ ] Concurrent contracts have explicit accounting, execution and trust semantics.
- [ ] Supported standard synchronization primitives expose reviewed trusted or
      verified contracts; users need not re-prove their implementations.
- [ ] Mutex guard and semaphore permit semantics include identity, acquisition,
      release, supported outcomes and capacity effects.
- [ ] Guarantees supplied by Rust/Verus are distinguished from memory-lifetime
      and byte-bound obligations established by Verus Meter.
- [ ] Executable lifetimes are automatically related to synchronization states,
      including explicit/implicit guard release and allocations inside helpers.
- [ ] Symbolic worker counts and buffer sizes contribute to checked total bounds.
- [ ] Spawning, captures, waiting workers, completion and joining preserve storage.
- [ ] Supported sharing and ownership transfers neither lose nor duplicate charges.
- [ ] User-defined synchronization proofs constrain actual allocation lifetimes.
- [ ] Both exclusive and bounded-parallel overlap constraints produce tighter bounds.
- [ ] Helpers preserve the synchronization and ownership facts needed for composition.
- [ ] Instance and acquisition identities remain precise through aliases, calls,
      returned values, closure captures and thread boundaries.
- [ ] Several allocations or shared views under one guard do not receive duplicate
      per-holder allowances; primitive storage and workspace remain counted.
- [ ] Allocations retained after unlock or worker completion remain accounted for.
- [ ] Adding an executable allocation changes the generated memory obligations
      without requiring a manual ghost-counter update.
- [ ] Negative tests reject too-small bounds, allocation before acquisition,
      early release, unrelated lock instances and extra simultaneous buffers.
- [ ] Standard primitives and custom verified protocols both have positive and
      negative integration coverage, including acquisition outcomes and reacquisition.
- [ ] Tests cover retained results, shared storage and ownership transfers across
      function and thread boundaries, as well as sequential regressions.
- [ ] Unsupported operations fail explicitly; diagnostics and documentation describe
      the completed supported boundary.
- [ ] Required validation passes against the built verifier, with material gaps
      resolved before marking the core complete.

## Scope decisions to settle in the detailed TODOs

Agree on concrete supported operations before implementation: thread APIs,
shared-ownership operations, standard mutex operations, concrete semaphore APIs,
atomic primitives and ordering guarantees, and supported ways of expressing
synchronization proofs. Specify each library contract's identity, trust source,
release/error behavior and modeled storage effects. Supporting user-defined
protocols does not mean that every Rust primitive is already modeled.

Also settle the treatment of nested spawning, detached workers, panic/unwinding,
custom destructors, channels, async cancellation and delayed reclamation. The
previous assessment recommends restricting several of these initially; those
recommendations are not an agreed scope decision. Record each as required for
core completion or explicitly outside the core, with a reason. Do not silently
omit them or call an incomplete requirement finished.

## Execution order and tracking

Design the accounting semantics, reusable synchronization contracts, automatic
lifetime relationships and summary interface together first. Then build the
thread accounting and proof integration, complete composition and symbolic bound
checking, and finish the full validation matrix.
Add regression tests alongside each behavior rather than waiting until the end.

Each numbered TODO identifies the work it delivers, its dependencies and concrete
completion evidence; the TODO index maps that work to this checklist. Keep this
checklist as the single overview of what remains. Implementation commits can be
incremental while the definition of core completion stays fixed; scope changes
must be explicit.
