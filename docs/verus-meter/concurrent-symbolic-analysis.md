# Synchronization-aware symbolic peak memory for concurrent Rust

## Assessment

A practical extension is feasible, but multiplying existing function peaks by a
thread count is not an adequate foundation. Preserve the existing source-storage
analysis and extend its lifetime profiles into **protocol-indexed simultaneous
footprints**. Prove that each executable allocation belongs to a live footprint,
and that the verified synchronization protocol restricts the combinations of
footprints that can coexist. Check a symbolic upper bound over those combinations.

The central proof is a safety invariant over every execution prefix, not a search
for one worst scheduling trace. Developers should supply protocol invariants and
arithmetic lemmas; the compiler must supply allocation events, sizes, ownership
transfers, and releases. A manually incremented ghost byte counter cannot establish
the required connection on its own.

This should yield exact temporary-storage bounds for mutex exclusion, bounded
parallel phases, and selected pipelines. Exact whole-program bounds will also
depend on frame storage, pending results, handles, and the precision of helper
summaries. There is no practical promise of mathematically optimal bounds for
arbitrary Rust programs. In particular, proving an upper bound does not prove that
some execution attains it.

This assessment examines repository revision
`f9c4b8beb3a13a8cdca8185aae6c708733ac5bbb`. It proposes changes; it does not implement
or verify concurrent memory support. All source links are repository-relative.

## Existing implementation and reusable foundations

The authoritative [memory model](../model.md) is a source-level byte model, currently
named `source-values-v38-64` in
[model.rs](../../source/vir/src/resource/memory/model.rs). It assumes eight-byte
words, sums struct fields without ABI padding, excludes ghost/proof storage, and
does not describe physical stacks, allocator metadata, fragmentation, or RSS.
Concurrency must retain these qualifications. OS thread stacks cannot silently be
included in a claimed source-storage guarantee.

### Pipeline and proof generation

| Layer | Current implementation and consequence |
| --- | --- |
| Syntax | [syn resource syntax](../../dependencies/syn/src/verus.rs), [macro lowering](../../source/builtin_macros/src/resource/memory/mod.rs), and [frontend budget lowering](../../source/rust_verify/src/resource/memory/budget.rs) represent resource clauses and queries. Keep ordinary scalar byte contracts as the public endpoint. |
| Frontend integration | [query.rs](../../source/rust_verify/src/query.rs) calls the [memory pipeline](../../source/rust_verify/src/resource/memory/pipeline.rs) on mode-checked, unsimplified VIR. This preserves places and control flow needed for accounting. |
| Analysis | [check_crate](../../source/vir/src/resource/memory/mod.rs) resolves layouts/budgets, checks a call graph, builds summaries, and only then instruments proofs. Unsupported executable operations are errors. |
| Proof obligations | [symbolic.rs](../../source/vir/src/resource/memory/symbolic.rs) inserts ordinary assertions, range checks, and erased model state. Memory annotations are subsequently erased; they do not become assumptions. |
| Arithmetic | [contracts.rs](../../source/vir/src/resource/memory/contracts.rs) implements substitution, conditional formulas, addition, multiplication, minimum and maximum. Formula arithmetic is mathematical but evaluated budget expressions must fit `u64`. |
| Storage algebra | [footprint.rs](../../source/vir/src/resource/memory/footprint.rs) preserves correlations through addition, maximum and removal, with separate `host.local` and `host.heap` charges. Source contracts currently select total memory. |

These are directly useful for symbolic thread counts, capacity parameters, and
proofs under preconditions. They are not already a concurrent semantics. Ordinary
local proof assertions cannot access a coherent, mutable snapshot of other
threads merely by introducing more ghost variables.

### Ownership, lifetimes, and summaries

[accounting.rs](../../source/vir/src/resource/memory/accounting.rs) tracks live
values, symbolic allocations, input lifetimes, alternative paths, and simultaneous
cost points. Its `call_cost_with_inputs` substitutes particular input/result
lifetimes at a peak witness. These points describe sequential executions, not
scheduler states.

[heap.rs](../../source/vir/src/resource/memory/heap.rs) separates lexical slots
from owned allocation trees. Fixed children have structural paths; runtime
children have aggregated footprints. Borrowed incoming allocations remain charged
to the caller, while replacements are charged locally. Flattening an owner tree
preserves disjoint provenance rather than copying its charges.
[lifetime.rs](../../source/vir/src/resource/memory/lifetime.rs) transfers value
identities on moves and distinguishes early scratch from later results.

[FunctionSummary](../../source/vir/src/resource/memory/summary.rs) already combines
modified parameters, allocation and vector facts, input paths, return forwarding,
transfer templates, and lifetime profiles. A `Profile` contains a footprint,
input identities and whether the result is live. It does **not** contain a thread
identity, protocol state, lock identity, or transition relation.
[transfer templates](../../source/vir/src/resource/memory/transfer/mod.rs) describe
parametric transformations of ownership forests. Preserve this stronger interface:
a scalar byte allowance cannot replace an ownership summary.

[growth.rs](../../source/vir/src/resource/memory/growth.rs),
[loops.rs](../../source/vir/src/resource/memory/loops.rs), and
[metadata](../../source/vir/src/resource/memory/metadata.rs) supply compiler-owned
capacity snapshots, retained-byte state and inductive loop obligations. These are
precedents for generated concurrent proof state, though a local loop invariant is
not an interference-stable concurrent invariant.

Important limitations are explicit in [eligibility](../../source/vir/src/resource/memory/model.rs)
and [call handling](../../source/vir/src/resource/memory/calls.rs): checked ordinary
calls require safe, nongeneric, local verified functions with resource contracts.
The [call graph](../../source/vir/src/resource/memory/call_graph.rs) rejects cycles.
Async functions, shared ownership, arbitrary closures, generic concurrency APIs,
custom destructors and imported memory summaries are not covered by the current
memory interface. Adding `spawn` as an ordinary call would be unsound: its work
continues after that call returns.

### Evidence from tests

The [resource test suite](../../source/rust_verify_test/tests/resource/memory/mod.rs)
and [examples](../../examples/resource/memory/README.md) establish useful sequential
regression boundaries:

- [lifetimes.rs](../../source/rust_verify_test/tests/resource/memory/lifetimes.rs)
  distinguishes early scratch/late results, explicit drop, retained incoming
  allocations and releases through nested calls.
- [return_sharing.rs](../../source/rust_verify_test/tests/resource/memory/return_sharing.rs)
  checks single charging across moves/forwarding, independent fresh allocations,
  copies, and preservation of dynamic vector reservations.
- [storage_calls.rs](../../source/rust_verify_test/tests/resource/memory/storage_calls.rs)
  checks sequential reuse, caller overlap, contract slack, missing contracts and
  recursive-call rejection.
- [reachability.rs](../../source/rust_verify_test/tests/resource/memory/reachability.rs)
  demonstrates that preconditions and loop invariants discharge generated cost
  assertions, including rejecting reachable excessive allocations.
- [growth.rs](../../source/rust_verify_test/tests/resource/memory/growth.rs),
  [conditional_loops.rs](../../source/rust_verify_test/tests/resource/memory/conditional_loops.rs),
  and [incoming_children.rs](../../source/rust_verify_test/tests/resource/memory/incoming_children.rs)
  exercise capacity/ownership and loop integration boundaries.

These were inspected, not rerun for this documentation task. They do not establish
concurrent memory soundness. The new tests should extend their distinct lifetime
cases across spawn, synchronization and join boundaries.

## What Verus concurrency already supplies

[vstd/thread.rs](../../source/vstd/thread.rs) wraps `std::thread::spawn` and join in
external bodies. Spawn requires a callable `FnOnce`, `Send` and `'static`; the
handle carries a predicate on successful returned values. Join returns
`Result<Ret, ()>`. Neither interface specifies memory, outstanding worker counts,
or the storage retained by a completed but unjoined worker. Thread identity proof
objects have explicit thread-sharing restrictions. This is a functional and
ownership foundation, not a peak-memory summary.

[vstd/invariant.rs](../../source/vstd/invariant.rs) provides shared atomic
invariants and non-shared local invariants. An atomic invariant can be opened
around at most one permitted atomic operation, not around arbitrary allocation or
an entire critical section. [modes.rs](../../source/vir/src/modes.rs), notably
`AtomicInstCollector`, enforces atomic-operation restrictions.
[atomic_ghost.rs](../../source/vstd/atomic_ghost.rs) connects ghost state to
sequentially consistent atomic values. Do not weaken those rules to make a global
memory counter convenient.

The verified [RwLock](../../source/vstd/rwlock.rs) is especially relevant. Its
tokenized state machine distinguishes pending readers/writers, acquired readers,
an exclusive writer, and protected storage. Atomic ghost updates connect state
transitions to actual atomics; cell permissions connect access to executable data.
Write/read handles require explicit release: dropping a handle does not unlock
this implementation. A memory adapter must use those actual semantics, rather
than assume standard RAII mutex behavior. Its public value predicate alone does
not express the lifetime of unrelated scratch allocated while holding the lock.

[Atomic increment examples](../../examples/atomic_increment.rs) also use logically
atomic update interfaces. These can expose protocol transitions at linearization
points, but an operation's temporary memory can exist before and after that point.
A linearizable functional specification alone is insufficient for peak memory.
The [thread example](../../examples/thread.rs) and
[atomic counting state machine](../../examples/state_machines/tutorial/counting_to_n_atomic.rs)
illustrate thread identity and inductive counting separately; neither is a memory
proof. Ordinary [Arc specifications](../../source/vstd/std_specs/smart_ptrs.rs)
describe values, not allocation identity, reference counts, or reclamation costs.

The inspected vstd surface does not provide an immediately reusable resource
adapter for mutexes, semaphores or channels. They require explicit models, even
where ordinary functional verification can already describe their behavior.

## Proposed semantic foundation

Define a resource scope covering a coordinator and all participating descendants.
For every modeled execution prefix, let `A` be its live allocation identities and
`V` its live inline value/slot identities. Define:

```text
M(state) = sum(bytes(a), a in A) + sum(bytes(v), v in V)
peak(scope) = supremum M(state) over all permitted prefixes in the scope
```

The identities are semantic bookkeeping, not machine addresses. Reusing an
address does not identify an old and new allocation. Heap backing must remain in `A`, and inline storage in `V`, including storage
for shared roots, queued messages, captured closures and unjoined results, until
the corresponding modeled release. These sets define the theorem; implementing a
literal global set or inserting a runtime counter is unnecessary.

For composition, summarize each worker by protocol phases and their simultaneous
footprints, including incoming ownership and outgoing retained storage. For a
state abstraction `q`, prove:

```text
I(q)                         verified protocol invariant
Coverage(execution, q)       generated charges cover every live modeled object
M(execution) <= E(q, inputs) compiler-derived simultaneous footprint envelope
I(q) ==> E(q, inputs) <= B(inputs)
```

Prove initialization and preservation of coverage and `I` for every admitted
transition. Use representative-worker proofs and aggregate phase counts for
homogeneous workers, rather than enumerate thread identities or schedules.
Other workers may step between local operations: local assertions may depend
only on stable facts, owned state, and correctly opened invariants. Abstract
interference must preserve the same global invariant.

For a mutex, a practical relation is:

```text
live scratch allocation owned by worker i
    ==> worker i holds an exclusive guard for lock instance L
number of holders of L <= 1
scratch bytes of each holder <= b
```

The first implication must be generated and checked against executable lifetimes.
It is the crucial missing bridge. Holding a guard at allocation time alone is
insufficient. Every exit, transfer, call and release must preserve the implication.
If scratch escapes, either reject this phase summary or move the allocation to an
explicit retained-storage class whose cost survives unlock.

A guard may cover several allocations: exclusion proves one **holder**, not one
allocation. The sum of that holder's simultaneous allocations must still fit `b`.
The compiler should derive that sum using the existing local analysis.

This design uses existing tracked protocol tokens as witnesses of synchronization,
not as consumable byte budgets. Some unforgeable connection between guard state
and allocation lifetime is necessary; excluding all proof witnesses would prevent
compositional reasoning about exclusion. There is no need to make developers
purchase an allocation with credits or choose a fixed capacity before verification.

## Precision and composition

### Thread counts and overlapping calls

For identical workers, an initial envelope can be:

```text
S + C(n) + n * W + n * T
```

Here `S` is shared storage counted once, `C(n)` is coordinator/control storage,
`W` bounds each worker's non-scratch storage, and `T` bounds scratch. These
components must be disjoint; an existing `peak(worker)` is not automatically an
incremental cost excluding shared input storage. With a proven mutex lifetime
relation the scratch term becomes `if n == 0 { 0 } else { T }`. With `k` permits it
becomes `min(n, k) * T`, provided permits cover full scratch lifetimes.

For four workers and `T = 4 * 1024 * 1024`, the temporary heap contribution is
4 MiB instead of 16 MiB. The entire program still pays for live frames, handles,
shared objects and other temporaries. A large source array used to initialize a
box may contribute additional local storage; do not call a 4 MiB heap contribution
a 4 MiB total bound without checking construction.

Use counts `c_p` for workers in phase `p` and an envelope such as
`S(q) + C(q) + sum(c_p * F_p) + R(q)`. Constraints relate phase counts, locks and
retained results. Unconstrained summation is one instance of this representation,
not a separate architecture preceding synchronization.

Sequential calls may reuse scratch; overlapping calls in different workers may
not. Nested call frames remain charged while blocked. A callee acquiring a lock
must expose pre-acquisition storage as well as its acquired phase. A helper that
returns an allocation requires a retained-result effect, not just a transient
peak. Avoid subtracting scalar peaks to infer savings: independently maximized
terms need not occur at the same time.

### Spawn, completion, and join

Count outstanding work from publication to completion, with capture and spawn
setup overlap included. Distinguish not-yet-started, running/blocked, completed
with retained result, and joined states. Joining transfers result ownership; it
does not allocate another copy of the result. Dropping a handle must not remove a
running worker from the bound. Initially reject detach and require a checked
structured join discipline, even if ordinary Rust permits more.

Dynamic spawning needs an invariant bounding simultaneous outstanding workers,
not necessarily total historical spawns. A pool can run indefinitely with bounded
workspace if each task releases its temporary state and queues/results are
bounded. Conversely, a fixed worker count does not bound an unbounded result
queue. Nested spawning needs descendant obligations and acyclic summary
dependencies initially. Parent scope exit cannot close the accounting scope while
descendants remain active.

### Shared ownership and transfer

Keep one charge per allocation identity and separate charges for each handle.
`Arc::clone` duplicates a handle, not the payload; release requires last-owner
semantics, including weak-reference/control-block behavior if supported. Initially
prefer a shared root retained by the coordinator until all joins, with a restricted
Arc adapter or a separately modeled scoped-borrow API. Scoped threads are not
provided by the inspected `vstd::thread` wrapper and are not a free shortcut.

Queue transfer changes who accounts for a payload, not whether it exists. Sender
pending data, queue backing, queued data, receiver data and retained outputs can
overlap. Model an in-flight transfer so that publication cannot create a gap or
a duplicate charge. Sequential reuse removes a charge only on a supported release;
last use, unlock, logical removal, or a protocol counter decrement does not itself
free memory. Reallocation must retain old/new overlap even under exclusion.

### Practical tightness

Start with finite phase sets, nonnegative affine envelopes and user-proved bounds
on counts. Support unequal worker sizes with symbolic sums or a supplied aggregate
lemma; `max_i T_i` suffices for a mutex but choosing the largest `k` sizes for a
semaphore may require stronger arithmetic proofs. Preserve cross-phase relations:
maximizing every component independently can lose the desired precision.

An invariant overapproximates reachable states. Optimizing over it can be sound
but loose because it admits unreachable combinations. Strengthening the invariant
or refining phases is the appropriate remedy. Automatic phase extraction and
simple algebraic simplification are realistic; automatic discovery of arbitrary
protocol invariants, nonlinear closed forms, or an optimal schedule is not.
General optimal bounds would require solving arbitrary program reachability and
termination-dependent storage questions. Even finite abstractions can have an
exponential product of worker phases; nonlinear arithmetic and quantified
ownership sums add proof complexity. Use aggregation and explicit refinement
limits, reporting precision loss when a coarser envelope is used. Treat solver
timeout as unproved, never as permission to assume the bound.

## Synchronization mechanisms

| Mechanism | Required connection and precision boundary |
| --- | --- |
| Mutex/exclusive RwLock | Stable instance identity and exclusive guard ownership; scratch lifetime contained in the acquired interval. Read guards do not provide mutual exclusion between readers. |
| Semaphore | Verified permit conservation and `holders <= k`; a permit must remain held while its attributed scratch lives. Reserving before allocation can safely overapproximate occupancy. |
| Atomics/spin locks | Successful CAS must establish the relevant phase/guard; failed CAS and retries establish no ownership. Initially use the existing sequentially consistent atomic library. Relaxed ordering needs a separately justified memory-order model. |
| Channels | Bound payload sizes and all queue/in-flight/consumer ownership. Bounded queue length alone does not bound blocked producers' preconstructed messages or receiver-retained data. |
| Barriers | Prove every participant has released phase-A storage before phase-B storage can appear, including repeated barrier generations. Arrival does not imply release. |
| Condition variables | Include wait releasing and reacquiring the lock, recheck predicates after wakeups, and retain waiter storage throughout. Initially defer. |
| Lock-free reclamation | Logical removal and CAS success do not imply deallocation. Retired nodes, hazards and epochs can retain arbitrarily much storage without further bounds; defer until modeled explicitly. |

Never hold an atomic invariant open around an allocation. Instead, acquisition
establishes a durable exclusive protocol witness at its atomic transition; local
allocation proofs use that witness after the invariant has closed. Release is
permitted only when the compiler-derived attributed footprint is empty or has
been transferred to a charged persistent class. A useful first implementation can
check this containment structurally, while a later general implementation uses
verified transition summaries.

## Architecture and soundness obligations

Keep fork-specific implementation under `vir::resource::memory`, with thin
frontend hooks. The following are proposed additions, not existing APIs:

1. **Concurrency event IR.** Add explicit spawn/publication, completion, join,
   synchronization acquire/release, transfer, allocation and release events with
   source spans, ownership identities and protocol-instance identities. Preserve
   evaluation order and transient old/new overlap. Existing `MemoryEvent` is a
   diagnostic trace, not a sound executable event IR by itself.
2. **Protocol-indexed summaries.** Extend `FunctionSummary`/`Profile` with phases,
   stable guards, owned input/output regions, retained effects and permitted
   transitions. Calls instantiate lock identities and captured arguments as well
   as scalar parameters. Keep existing scalar contracts as coarse projections;
   tight consumers need an explicitly checked richer interface, not inference
   from undocumented properties of a callee body or its scalar slack.
3. **Worker and closure summaries.** Model closure environment construction/moves,
   capture storage, invocation and result retention. Separate asynchronous spawn
   edges from ordinary call edges. Start with restricted noncapturing worker
   adapters plus explicit supported captures, rather than arbitrary higher-order
   calls. Version any imported summaries against the memory model and assumptions.
4. **Generated coverage proofs.** Extend allocation provenance across workers and
   shared roots. Generate phase-footprint and count relationships from executable
   events. Integrate with tracked state machines and invariant opening without
   inventing shared mutable spec variables that Verus treats as thread-local.
5. **Protocol adapters.** Identify primitives by resolved compiler/library
   identity, as existing [intrinsic recognition](../../source/rust_verify/src/resource/memory/intrinsics.rs)
   does. Verify adapter code when possible. Audit trusted external spawn, join,
   allocation and synchronization semantics explicitly; a function named `lock`
   must never acquire trusted exclusion semantics automatically.
6. **Bound checking and diagnostics.** Generate ordinary assertions that each
   allowed simultaneous envelope fits the supplied expression. Diagnose a missing
   lifetime/ownership interface separately from an unproved numeric bound. Show
   contributing allocations, phases, lock identities and retained results.

The soundness argument must cover all modeled execution prefixes, including
blocked threads and incomplete calls. Check before/after transitions and internal
transient peaks, not only at synchronization boundaries. For each primitive prove
that its abstract transitions simulate executable behavior. Local transition
proofs plus interference-stable protocol invariants then compose across workers.

A first release should restrict to successful allocations and a clearly specified
non-unwinding execution model. It must prove/restrict ordinary panic paths or
state an explicit execution-domain restriction; merely ignoring `join`'s error
case is insufficient. Catch-and-continue unwinding, poisoning, cancellation and
custom destructors require separate storage semantics. On unsupported paths,
reject coverage rather than pretend a zero cost. Abort/OOM behavior must be stated
consistently with the source model and must not imply a physical-memory guarantee.

Prevent user ghost code from deleting coverage records, assigning sizes, or
forging protocol-instance matches. Proof functions may establish lemmas about
compiler-owned observations but may not create unchecked accounting facts.
Existing Verus trust escape hatches (`assume`, external bodies and specifications)
remain trust assumptions; keep the demonstration's coverage and protocol proof
free of user-added assumptions and audit trusted adapters separately.

Reject forgotten/leaked owners until modeled as permanently retained storage.
Account for sync-object storage and executable library work through explicit
source-level primitive rules or verified bodies. Avoid silently applying functional
external specifications as zero-memory contracts. Atomics do not make all the
operations between them indivisible, and Rust `Send`/`Sync` alone says nothing
about how many allocations coexist.

## Proposed proof of concept and acceptance criteria

Use a coordinator creating `n` workers, a single shared exclusive lock, and one
`Vec<u8>::with_capacity(b)` per worker. An empty vector still owns backing storage
in this model, so this isolates the allocation without a large initializer array.
The following ordinary Rust example defines the executable behavior to target.
It is not a currently verifiable Verus Meter example: `Arc`, mutexes, spawn
closures, join and their library internals need the adapters described above.
The eventual Verus version should use a verified exclusive protocol (for example,
a restricted adapter over the vstd RwLock writer protocol), with equivalent
allocation and release ordering.

```rust
use std::sync::{Arc, Mutex};
use std::thread;

pub fn run(n: usize, b: usize) {
    let lock = Arc::new(Mutex::new(()));
    let mut handles = Vec::with_capacity(n);

    for _ in 0..n {
        let worker_lock = Arc::clone(&lock);
        handles.push(thread::spawn(move || {
            let guard = worker_lock.lock().unwrap();
            let scratch = Vec::<u8>::with_capacity(b);
            drop(scratch);
            drop(guard);
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
```

Remove the guard acquisition and release for the unconstrained variant. Move the
constructor before acquisition or the scratch drop after release for the lifetime
negative variants. All allocate actual vector backing in the source model; no
ghost counter substitutes for the constructor. The Rust sketch's `unwrap` paths
must be replaced by proved-success handling or covered by the explicit execution
domain of the future proof. This sketch was type-checked as a library using the
repository's pinned Rust toolchain; that check is not memory verification.

Use supported integer inputs with explicit multiplication/range preconditions.
The future full example must declare its lock predicate/state machine, match all
instances, handle API result cases and prove loop invariants for spawned/joined
counts. Give workers unit results to avoid result-buffer retention initially.

Generate a scratch footprint `X` from the actual vector backing events. Independently
derive an envelope `H(n,b)` for all other storage: shared root/control block,
coordinator frame, handle-vector capacity, closures, worker frames, guard storage,
spawn/join transient workspace and permitted library costs. Do not make `H` a
user-assumed constant. Its formula can be conservative; its contributors must be
visible in generated diagnostics and covered by checked summaries. These are the
proposed acceptance assertions:

```text
Without a proven exclusion/lifetime relation:
    peak scratch <= n * b
    peak total   <= H(n,b) + n * b

With one shared exclusive lock and contained lifetimes:
    peak scratch <= (if n == 0 then 0 else b)
    peak total   <= H(n,b) + (if n == 0 then 0 else b)
```

A scratch projection is a proposed compiler-defined allocation group, not a
current source query and not an exemption from checking total memory. It is useful
for exact negative tests: subtracting one byte from a loose total envelope may
still yield a valid bound. For `n > 0` and `b > 0`, a scratch claim of `b - 1`
must fail at the constructor. A total-memory negative test must use an independently
established necessary live footprint, not blindly subtract one from `H + b`.

Require these paired verification outcomes:

| Variant | Required outcome and reason |
| --- | --- |
| No lock, `n*b` scratch claim | Pass with symbolic count invariant. |
| No lock, `b` scratch claim, `n >= 2`, `b > 0` | Fail: workers can pause after allocation and overlap. |
| One shared lock, allocate/drop before release | Pass the tighter symbolic claim. For `n=4`, `b=4194304`, scratch is at most 4194304 bytes. |
| Same locked code, scratch claim `b-1` | Fail on the generated allocation obligation. |
| Allocate before acquiring the lock | Fail the tight claim: waiting workers retain their buffers. |
| Release the guard before dropping scratch | Fail containment or the tight bound; unlock cannot release a heap charge. |
| Move scratch to a returned value or shared collection before unlock | Retain its charge; reject the transient-only profile or reject the tight bound. |
| Give each worker a different lock | Fail exclusion for the common scratch group despite identical lock types. |
| Add a second simultaneously live `Vec` under the guard | Fail `b` scratch claim; mutual exclusion permits one worker owning two buffers. |
| Forgo release by forgetting an owner, or detach a worker | Reject unsupported lifetime/scope handling initially. |

The abstract arithmetic lemma alone is not the demonstration. Compiler-generated
allocation/provenance evidence must be mandatory, and changing executable code in
these variants must change the proof obligations without manually updating ghost
allocation counters. For the unconstrained negative case, a legal witness schedule
pauses all workers just after allocation; for the mutex positive case, induction
proves the bound for every schedule without requiring fairness. Small model-based
schedule tests may help find adapter mistakes, but cannot replace the unbounded
symbolic proof.

## Phased implementation plan

1. **Specify the concurrent model and adapter trust boundary.** Define scope,
   event ordering, coverage, worker states, shared identity, panic restrictions and
   primitive costs. Design protocol-indexed profiles before implementing summed
   worker bounds. Review the allocation-before-lock and escape-after-unlock cases
   as semantic litmus tests.
2. **Deliver the smallest synchronization-aware vertical slice.** Restricted
   structured workers, one exclusive protocol, unit results, one supported dynamic
   buffer, explicit drop, stable shared root. Add closure/capture and spawn/join
   accounting sufficient for the example. Check both `n*b` and `b` via the same
   profile algebra. This milestone is incomplete without executable mutation
   failures and automatically derived non-scratch charges.
3. **Make local helper composition preserve precision.** Carry guard identity and
   lifetime effects through ordinary calls, nested scopes, branches, replacements
   and returned values. Preserve existing sequential summary behavior. Add failure
   cases for retained inputs, wrong-instance substitution, hidden helper allocations
   and same-span transient overlap.
4. **Add bounded parallel phases.** Semaphores, heterogeneous symbolic costs,
   phase-count invariants and selected barriers. Let users prove aggregate lemmas
   and strengthen protocol invariants. Keep inference focused on common patterns;
   allow explicit checked profiles where inference is insufficient.
5. **Extend ownership domains and worker lifecycles.** Model Arc reclamation,
   non-unit join results, bounded channels, nested/dynamic spawning and task pools.
   Require live-worker/queue/result invariants. Add scoped-thread adapters only
   with their own lifetime and primitive semantics.
6. **Expand the execution boundary deliberately.** Imported versioned summaries,
   generic interfaces and more synchronization libraries precede detached work,
   async cancellation, unwinding or lock-free reclamation. Each needs a coverage
   argument; none should be enabled by accepting a scalar bound alone.

For implementation milestones, run the repository's prescribed memory unit,
verifier-build, integration and example checks. Frontend/closure/invariant changes
also require affected parser/prettyprinter and upstream regressions, especially
modes, erasure, references and function contracts. Use Rust test orchestration.
No implementation checks are claimed for this report.

## Alternatives and final recommendation

Independent peak summation is useful as a fallback when footprints are disjoint
and no synchronization facts are known. It loses exactly the information required
for the motivating example, so it should be a projection of the richer design.
Explicit interleaving exploration can validate tiny examples but does not scale to
symbolic thread counts; prefer inductive protocol proofs. Whole-program inlining
may recover correlations but defeats practical compositionality.

Memory credits can help enforce a fixed capacity under open-ended spawning or
admission control. That solves a different interface problem: authorization to
consume a bounded pool. They are unnecessary for proving the mutex scratch bound
and would move burden from executable lifetime analysis to manual resource
bookkeeping. Keep them optional for programs that actually implement such a pool.
Likewise, existing synchronization permissions are useful evidence, but need not
become a new allocation-permission API.

Proceed with compiler-derived lifetime footprints composed under verified
synchronization invariants. Preserve symbolic byte contracts, ownership provenance
and generated Verus assertions. Make the first usable slice prove the tighter
mutex bound and reject incorrect lifetime variants; otherwise it will validate
thread arithmetic without addressing the central concurrency problem.
