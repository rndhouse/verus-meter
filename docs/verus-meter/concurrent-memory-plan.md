# Concurrent peak memory verification: assessment and implementation plan

Verus Meter can be extended to prove system-wide peak memory bounds for a
restricted subset of concurrent Rust. The practical approach combines its existing
allocation accounting with Verus tracked ghost resources and synchronization
proofs. The initial guarantee should cover every execution of a verified
concurrent subsystem under Meter's source-level memory model.

General Rust concurrency, arbitrary async runtimes, and physical allocation success
require additional stages. Automatically finding the tightest bound for arbitrary
programs is not a realistic objective; proving useful bounds from supplied
synchronization invariants is.

This assessment is based on inspection of the accounting pipeline, ownership
summaries, proof libraries, concurrency examples, and async specifications. It does
not report newly executed verifier tests or an implemented concurrency extension.

## Existing capabilities

The authoritative [memory model](model.md) already provides:

| Capability | Relevance to concurrency |
| --- | --- |
| Live and peak accounting for local storage and heap allocations | Supplies costs that concurrent protocols must conserve |
| Allocation provenance and ownership transfers | Moves allocations between workers without duplicating payload charges |
| Nested ownership and collection footprints | Describes messages containing multiple owned allocations |
| Capacity accounting and overlapping old/new allocations | Covers growth, replacement, and temporary storage |
| Call summaries with retained-input and result lifetimes | Provides a foundation for worker contracts |
| Checked loop invariants and storage reuse | Supports long-running workers without charging cumulative allocation volume |
| Conditional budgets and verified specification formulas | Supports parameterized workers, buffers, and channel capacities |
| Internal `host.local` and `host.heap` identities | Enables later distinctions between source storage and allocator capacity |

The [memory pass](../../source/vir/src/resource/memory/mod.rs) operates on
mode-checked, unsimplified VIR. It checks structural accounting rules and generates
ordinary Verus assertions through the
[frontend integration](../../source/rust_verify/src/resource/memory/pipeline.rs).
Unsupported operations fail rather than receiving zero cost.

The [memory proof library](../../source/vstd/std_specs/resource/memory/mod.rs)
contains allocation-forest validity, partitioning, selection, and cost lemmas.
Executable examples demonstrate
[ownership handoffs](../../examples/resource/memory/heap/ownership.rs) and
[release-before-replacement reuse](../../examples/resource/memory/heap/loops/peak_overlap.rs).
These proofs do not establish end-to-end formal soundness of Meter's compiler
pass; that implementation remains part of the trusted verification machinery.

Current resource-checked functions must be safe, nongeneric, locally verified
functions with an acyclic call graph. Shared ownership, custom destructors,
imported resource summaries, and async functions are unsupported. Layout checking
also rejects invariant-bearing structs and ghost/tracked struct fields. A credit
library alone therefore cannot provide concurrent Meter verification; compiler
integration is necessary.

## Reusable Verus concurrency support

This checkout contains [thread spawn/join specifications](../../source/vstd/thread.rs),
[tracked resource algebras](../../source/vstd/resource/pcm.rs), atomic invariants,
atomic operations coupled to ghost state, and a verified reader/writer lock.
Examples include [reference counting](../../examples/state_machines/arc.rs) and a
[bounded SPSC queue](../../examples/state_machines/tutorial/fifo.rs).
[Future specifications](../../source/vstd/future.rs) support functional async
reasoning but do not describe retained memory.

These are building blocks, not existing Meter memory guarantees. Spawn/join
wrappers have trusted bodies. Verus tokenized state machines provide an appropriate
foundation for protocols involving locks, reference counts, and concurrent queues;
see the [Verus concurrency guide](https://verus-lang.github.io/verus/state_machines/).

## Global conservation theorem

Let `L(s)` be modeled live storage in reachable global state `s`, counting each
allocation once. The target is `L(s) <= B` for every reachable state.

Prove this through an inductive invariant rather than schedule enumeration:

1. Every live allocation and modeled local-storage obligation has budget coverage.
2. Credits originate from one budget domain of size `B`.
3. Allocation consumes available credits; verified deallocation enables reuse.
4. Transfers move responsibility without creating credits.
5. Every program transition preserves these properties.

Conceptually:

```text
L(s) <= charged(s)
charged(s) + reserved(s) + free(s) + lost(s) = B
```

Reservations may conservatively cover future workspace. Lost credits represent
discarded capabilities that cannot be reclaimed: discarding ghost state must never
create available memory. This proves a bound over every finite execution prefix,
including stalled executions. Fairness, deadlock freedom, and eventual completion
are separate properties.

Meter must connect credits to every supported allocation, release, transfer, and
retained object. A user-written bounded ghost counter without that connection is
insufficient. Use nonduplicable tracked capabilities for budget authority and
ordinary ghost values for descriptive metadata. Allocation-forest descriptions
supply costs but are not exclusive spending authority. Capabilities must carry a
budget-domain identity so fresh ghost resources cannot mint additional allowance.

Rust moves transfer exclusive responsibility; borrowing preserves responsibility
with the owner. `Send` and `Sync` constrain cross-thread transfers. However, ending
a borrow does not deallocate storage, blocked threads retain locals, and safe Rust
can leak memory. Channel sends and receives transfer charges. An `Arc` clone adds
a handle rather than another payload; reclamation must wait for the relevant
shared lifetime to end.

## Synchronization-dependent reuse

Tight bounds require proofs about which allocations can coexist. Four workers
needing 4 MiB scratch each can share one 4 MiB allowance when a verified exclusive
permit enforces acquisition before allocation and release after deallocation.
The permit must correspond to executable synchronization: erased ghost state
cannot serialize executable code.

A bounded channel limits queued messages, not producer-held pending messages,
consumer-held messages, internal staging, or queue backing. All require coverage.

Atomic invariants connect ghost transfers to synchronization operations. This
checkout restricts their opening to a single sequentially consistent atomic
operation. Acquire a capability atomically, close the invariant, and retain that
capability throughout subsequent allocation or blocking work; do not hold an
atomic invariant open across arbitrary operations.

## Proposed architecture

Extend the current system at four boundaries:

| Extension | Responsibility |
| --- | --- |
| Meter accounting and summaries | Connect storage events to credits and describe retention, transfer, and release |
| Verus memory-resource library | Define domains, exclusive credits, allocation receipts, conservation lemmas, and protocol invariants |
| Resource-aware concurrency adapters | Specify spawn/join, channels, permits, shared ownership, and task scheduling |
| Root verification and diagnostics | Establish subsystem coverage and identify failed budget or protocol obligations |

Preserve existing local `resources peak(memory)` semantics. Introduce an explicit
global-budget root or scope rather than silently changing every function allowance.
Extend the [function summary](../../source/vir/src/resource/memory/summary.rs) with
required and returned capabilities, exported resources, and storage retained across
blocking or suspension. A scalar peak alone cannot describe these effects.

Keep ownership forests for uniquely owned allocations. Add shared allocation
identities with one charge per allocation. Initially recognize a small explicit
set of resource-aware primitives; arbitrary external specifications must not bypass
accounting. Export versioned cross-crate summaries once semantics stabilize.

Meter currently runs after mode checking. Generated tracked operations must undergo
relevant mode and ownership checks; inserting them as if they were ordinary
arithmetic assertions is insufficient. Explicit source-level tracked APIs are a
sensible first step, followed by automation. Ghost accounting should erase without
runtime counters; executable synchronization remains necessary where the program's
reuse protocol requires it.

## Smallest meaningful demonstration

Start with two workers, fixed-capacity SPSC channels, restricted spawn/join, and an
exclusive scratch permit. Adapt the existing queue proof pattern. Fix the sharing
lifetime of queue infrastructure to avoid requiring general `Arc` reclamation.
The proof must cover executable buffer allocation and transfer through Meter's
events; a standalone protocol theorem is only a mathematical precursor.

Then demonstrate the requested 16 MiB budget with:

| Component | Configuration | Payload allowance |
| --- | --- | ---: |
| Worker-held messages | Four workers, one 1 MiB buffer each | 4 MiB |
| Queued messages | Four SPSC channels, one slot each | 4 MiB |
| Producer pending message | At most one 1 MiB buffer across channels | 1 MiB |
| Scratch | One exclusive permit for a 4 MiB buffer | 4 MiB |
| Other modeled storage | Proved bound for backing, handles, locals, temporaries | <= 1 MiB |
| Total | | <= 14 MiB |

Use dynamically allocated, pre-reserved byte vectors with verified no-growth
behavior during processing. Avoid large local-array construction temporaries.
Workers drop each message before receiving another. The producer may retain one
message while blocked. Scratch is allocated after permit acquisition and freed
before permit release.

Required examples:

- Accept this configuration under 16 MiB.
- Reject two slots per channel: eight queued buffers, four worker buffers, one
  producer buffer, and scratch can coexist, totaling 17 MiB before other storage.
- Reject scratch allocation before permit acquisition.
- Reject permit return while scratch escapes to a caller or channel.
- Reject retaining a previous message across another receive without more credits.

The other-storage allowance must be proved, not assumed to cover unspecified
runtime behavior. Physical OS stacks and runtime internals remain outside this
abstract demonstration. Diagnostics should distinguish unsupported features,
insufficient proof information, and established budget conflicts: proof failure
alone does not establish an actual violating execution.

## Phased implementation

| Milestone | Capability and changes | Demonstrable proof |
| --- | --- | --- |
| 1. Sequential credit integration | Domain-bound credits and receipts tied to Meter events; required erased fields and resource interfaces | Allocation/drop reuse succeeds; duplicate spending, wrong domains, and premature refunds fail |
| 2. Fixed thread lifetimes | Restricted closure captures, spawn/join effects, retained results; initially prohibit detachment and unmodeled unwinding | Workers share a bound; join enables reuse; dropping a handle does not reclaim running-child allowance |
| 3. Channels and synchronized reuse | Queue transfers, pending sends, fixed backing, exclusive permits | The 16 MiB positive and negative examples |
| 4. Shared allocations and library contracts | Shared identities, clone/drop, final-owner reclamation, later weak references; versioned cross-crate summaries | Shared payload counted once and reclaimed at the correct lifetime boundary |
| 5. Suspended tasks | Explicit poll/state-machine tasks first; creation, pending states, results, cancellation, executor storage; later async lowering | Suspended buffers remain charged; higher task limits can invalidate a bound |
| 6. Fixed-capacity allocator | Pool or size classes with metadata, alignment, concurrency, and availability invariants; connect receipts to permissions | Every admitted request succeeds within an initialized fixed arena |
| 7. Broader allocator/platform coverage | General layouts, reallocation, fragmentation, caches, deferred frees, selected runtime and stack bounds | Stronger guarantees for a pinned implementation and environment |

Milestone 3 is the recommended initial delivery. Each stage should retain
sequential regressions and add failures targeting lost charges through errors,
pending sends, detached threads, retained results, and cancellation. Thread and
async integration also require upstream checks for closures, modes, erasure,
references, and function contracts, using the repository's documented checks.

## Async storage semantics

Functional async verification does not bound future storage. Account for captures
before first polling, locals and child futures across suspension, reachable heap
allocations, retained completed results, task headers, ready queues, wakers,
cancellation bookkeeping, and poll workspace across running executor workers.

Executor worker count does not bound suspended-task memory; task admission needs a
separate bound. A heap-allocated future frame retains its allocated extent even
when some fields are dropped. Charge that extent throughout the frame lifetime,
while separately owned allocations follow actual destruction. Explicit task state
machines expose these transitions; compiler-generated async lowering and `Pin`
require later integration.

## Allocator refinement and physical guarantees

Meter assumes 64-bit source storage, sums struct fields without ABI padding, and
uses its own collection-growth policy. A source-model bound does not imply an
equal bound on physical stacks, allocator consumption, virtual memory, or RSS.

Allocation success requires a stronger theorem:

```text
allocator invariant + request capability for a layout
    implies a suitable free block exists
```

Total live payload bytes alone cannot prove this: available bytes may lack a
suitably aligned contiguous block. Rust permits allocation failure for exhaustion
or unsupported layouts; see [GlobalAlloc](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html).

Start with fixed-size blocks or a few size classes. Charge rounded sizes and
metadata, reserving credits per class. General variable-sized allocation needs
block geometry and fragmentation invariants. Reuse
[layout facilities](../../source/vstd/layout.rs) and
[raw-memory permissions](../../source/vstd/raw_ptr.rs). The existing raw allocation
wrapper aborts on failure; its postconditions do not prove failure impossible.

The [Verus SOSP paper, section 4.2.4](https://verus-lang.github.io/paper-sosp24-artifact/assets/paper-20240921-162720-b7db935.pdf)
provides precedent for concurrent allocator verification. Its mimalloc case study
proves allocation correctness and non-aliasing, not this proposed fixed-budget
allocation-success theorem.

A verified 16 MiB arena establishes success conditional on initialization and
exclusive management. A process-wide physical guarantee additionally needs stack,
runtime, TLS, library, cache, and platform bounds. Allocator safety, allocation
success, and eventual completion remain distinct guarantees.

## Soundness risks and initial exclusions

- Every executable allocation path needs checked effects or an explicit trusted
  contract, including callbacks and library internals.
- Scope exit, unlock, send, join-handle drop, and cancellation request must not be
  mistaken for deallocation.
- Weak references, cycles, and deferred reclamation can retain shared storage.
- Panic, unwinding, spawn failure, channel closure, and cancellation need resource
  effects; initially restrict unmodeled paths and state assumptions explicitly.
- Reject `forget`, `ManuallyDrop`, raw ownership conversions, FFI allocation, and
  unsupported custom destructors until effects are modeled.
- Recursive spawning and unbounded tasks, queues, or outputs need admission
  invariants; recursion and generic layouts also exceed Meter's present boundary.
- Begin with supported synchronization semantics. Weak-memory atomics require
  justification beyond arbitrary sequential interleavings.
- Trust includes specifications, Meter's transformation, Verus, solvers, Rust
  compilation, and trusted primitive implementations. Disabling relevant proof or
  lifetime checks cannot support the claimed guarantee.
