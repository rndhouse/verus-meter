# Concurrent memory semantics and analysis interfaces

This is the implementation specification for the concurrent core, established by
TODO 01. It describes required behavior, not currently available verifier support.
The [memory model](../model.md) remains authoritative for existing sequential behavior;
[the implementation index](todo/concurrent/README.md) tracks delivery. Concurrency
must remain rejected until its coverage and bound obligations are implemented.

## Contract scope and execution domain

A contracted operation covers its frame, all workers it spawns transitively,
shared roots reachable through supported inputs, closure captures, and completed
results awaiting collection. Existing incoming-allocation conventions still apply:
borrowed incoming storage is charged by the enclosing caller, and summaries refer
to its provenance rather than creating another charge. The top accounting caller
must supply complete descriptors for shared roots; missing size/ownership facts are errors.
Its closed worker domain must include all executable users of those roots.
Unaccounted external workers that can mutate shared ownership are unsupported.

At function entry, charge modeled inline parameters and owned incoming regions
according to the existing model. At every execution prefix, the covered bytes are
the sum of distinct live inline-value identities and distinct live allocation
identities. Moves transfer identities; copies create inline charges. A handle and
its separately allocated payload are different storage. At return, owned results
transfer to the caller and remain charged there. Peak history includes their
construction. All descendant workers must be joined before the operation returns;
returned buffers and shared roots are allowed, live workers are not.

The theorem concerns every interleaving of the supported operations, including
blocked execution and nonterminating prefixes. No fairness or termination
assumption may justify releasing storage. At the top accounting operation, total
live modeled bytes must fit its declared bound at every prefix. At a helper boundary, preserve existing relative-cost
conventions: borrowed incoming regions are framed by the caller and composed with
the callee allowance/profiles, not silently included twice in that allowance.
A helper's scalar bound alone is therefore not an absolute bound on its borrowed
pointees. A verified upper bound need not be attainable and is not a claim about
physical RAM.

The core proves panic-free user execution, with successful allocation and thread
creation as explicit environmental assumptions. Allocator/OS failure terminates
this execution domain; no guarantee is made about failure reporting or unwind
storage. Within it, ordinary bounds/overflow/panic obligations must be proved.
Workers inherit this requirement: join errors are excluded by verified worker
behavior and trusted spawn/join semantics, not by assuming arbitrary postconditions.
Native joins also require ruling out self-joins and simultaneous cycles of join
waits: Rust permits platform panics in those cases. Join-safety obligations must
preserve the actual waiting caller and target identities across summaries and
symbolic populations. They do not establish termination of a worker or lock wait.
Locks constructed in the closed domain are initially unpoisoned; absence of
worker/user panic preserves this. An imported lock requires a checked unpoisoned
entry fact; without it, poison outcomes cannot be eliminated. Catch-unwind, panic
hooks, poisoning recovery and continuing after failure are outside the core.
Diagnostics must name these restrictions. External code cannot be treated as panic-free or memory-free without a reviewed contract.

## Supported operation matrix

These are core requirements. Monomorphized instances of the listed generic APIs
are supported for payloads with existing supported concrete memory layouts. This
does not enable arbitrary generic function resource summaries or arbitrary
higher-order execution.

| Surface | Required operations and restrictions | Owners |
| --- | --- | --- |
| Threads | `vstd::thread::spawn`, `JoinHandle::join`, and standard `std::thread::spawn`/`JoinHandle::join`; safe `move` FnOnce closures with supported concrete captures/results; symbolic spawn/join loops and acyclic nested spawning; all descendants joined | 03, 05, 07 |
| Shared ownership | `Arc::new`, `Arc::clone`, dereference/borrow, explicit/implicit drop, supported field/container moves, and `Arc::into_inner` for a proved unique canonical handle; strong references only; concrete supported payloads, including lock-protected owners; count final release and control storage | 03–05 |
| Standard mutex | `Mutex::new`, `lock`, `try_lock`, guard borrow/dereference/mutation, explicit/implicit guard drop; preserve protected payload ownership through supported operations; no mapped guards, raw access or poisoning recovery | 02, 04, 05 |
| Result handling | Primitive-specific `Result` matching and proved-success extraction for lock, try-lock and join; `WouldBlock` has no acquisition; poison paths cannot be silently discarded | 02, 03, 05 |
| Verified RwLock | vstd construction, exclusive acquire/release, shared acquire/borrow/release, and destruction through supported APIs; readers do not exclude each other | 02, 05, 06 |
| Semaphore | New reusable verified `vstd::resource::semaphore::Semaphore` and unit `Permit`: `new(k)`, blocking `acquire`, `try_acquire`, explicit `release`; immutable capacity, no split/merge/add/forget; acquire may block forever at capacity zero | 02, 06 |
| Protocol primitives | Existing vstd `PAtomicBool`, `PAtomicUsize` and corresponding `atomic_ghost` wrappers: new/load/store/compare-exchange/weak compare-exchange and supported checked counter operations; sequentially consistent ordering only | 02, 06 |
| Custom protocols | Safe concrete Verus functions, tracked guards/tokens, atomic invariants and tokenized state-machine proofs using those primitives; explicit transition/holder-bound proof interface described below | 02, 05, 06 |
| Payloads and helpers | Existing supported Box/Vec/boxed slices, concrete structures and ownership operations, plus the listed concurrency wrappers; safe local acyclic helpers with checked effects, including escaped buffers and guard returns | 03–05, 07 |

The verified `vstd::resource::semaphore::Semaphore` stores the available slots in
a sequentially consistent atomic word. Successful acquisition transfers one
linear witness to the returned permit. A failed compare-exchange can return
`None` under contention. Dropping a permit leaves its slot occupied. Calling
`Permit::release` returns exactly one slot to the issuing instance.

Custom raw-pointer/unsafe synchronization bodies require trusted contracts and
are outside verified-custom support. Relaxed atomics, arbitrary recursion,
cross-crate user effect summaries, scoped threads borrowing coordinator locals,
detached workers, arbitrary channels, condition variables, barriers, async work,
cancellation, Weak/raw Arc operations, cyclic ownership, custom Drop, and delayed
reclamation are outside the core. They add execution/ownership rules beyond the
selected interfaces. Reject their use in a covered executable path; do not assign
zero effects. Thread identity/trait rules still apply, including guards that
cannot be sent to another thread. Trust-escape features retain their existing
Verus meaning and must be visible in the trust audit.

## Library trust and source-storage policy

Standard Mutex exclusion and guard release are supplied by reviewed contracts
for resolved definitions, not re-proved from OS code. Rust documents
[guard-based access and poison outcomes](https://doc.rust-lang.org/std/sync/struct.Mutex.html)
and [guard destruction](https://doc.rust-lang.org/std/sync/struct.MutexGuard.html).
These guarantees do not relate unrelated buffers to a lock or prove a byte bound.
The blocking standard lock contract requires no outstanding acquisition of that
instance on the calling thread: reentrant locking has no guaranteed successful
behavior. Prove this requirement across helper calls or reject the call. Try-lock
retains its possible non-acquiring outcome instead of assuming success.
Existing Verus RwLock guarantees are reused with explicit release, as required by
[its actual interface](../../source/vstd/rwlock.rs).

Primitive contracts must separate behavioral effects from storage policy. Adopt
an explicit source abstraction for opaque runtime support, versioned with the
memory model, rather than pretending the layout is the platform ABI:

| Object | Required modeled source storage |
| --- | --- |
| Standard mutex | One 8-byte synchronization state, one poison-state byte, and the inline payload; separately owned payload allocations keep their identities |
| Standard mutex guard | One 8-byte reference; no payload copy |
| Supported PAtomic/atomic_ghost locations | One byte for Bool or eight bytes for Usize; associated permissions/invariants are tracked state and occupy zero bytes |
| Strong Arc | One 8-byte handle per live handle; one backing allocation with two 8-byte count fields plus inline payload and its owned descendants |
| Join handle | One 8-byte handle; separate completion storage for a one-byte state tag and inline result while retained; owned result allocations counted separately |
| Closure | Sum of executable capture fields, with moved payload identities transferred; invoking it transfers fields to worker storage without cloning allocations |
| Primitive Result | One-byte variant tag plus the maximum inline variant payload; active owning payload retains its separate allocations |
| Verified implementations | Sum of executable fields/locals and actual modeled operations under existing rules; tracked/ghost fields occupy zero bytes |

Completion storage is allocated at spawn publication, initially with its tag;
result inline storage becomes live when produced and stays until join transfers
it. Source temporaries for moving results and constructing wrappers follow existing
move/copy rules. Arc backing survives until the final modeled strong drop; no Weak
operations are admitted, so no subsequent weak-only retention is needed. Ownership
inside a mutex is one persistent shared root; moving it out or replacing it changes
its descriptor, not the number of copies charged.

Reviewed opaque primitive contracts have no additional source heap allocations
or internal frame workspace beyond this table, arguments, returned values and
explicit source temporaries. This is a deliberate abstraction of Rust/OS support,
not an upper bound on those implementations' physical internals. Their queues,
allocator metadata, OS stacks and ABI details are excluded just as physical stack
layout is excluded today. Verified library bodies do not receive this exemption.
Publish this policy and its size queries together; an unrecognized library call
has no such contract. Extend the model version when these rules are introduced,
without rewriting existing sequential type sizes or runtime query behavior.

## Events, identity and the effect graph

Extend `FunctionSummary` with a graph of control phases and effects, retaining
existing ownership templates and simultaneous `Profile` footprints. The graph is
a compiler-owned static abstraction, not a runtime trace or a mutable global ghost
counter. Ordinary source control and drop order determine its edges. A loop is a
back edge with an inductive summary, not an unrolling over concrete worker IDs.

Keep these distinct identity domains:

- **Allocation/value:** existing ownership provenance, fresh per construction;
  address reuse does not reuse an identity.
- **Synchronization instance:** fresh per lock/protocol construction, preserved by
  references, moves, Arc aliases and protected-cell identity. Unknown aliasing is
  conservatively unresolved; exclusion may be used only for proved common identity.
- **Acquisition:** fresh successful acquire event of an instance. Borrowed views
  alias it; moves transfer it; neither duplicates its capacity contribution.
- **Worker:** fresh spawn occurrence, with a family/index binder for symbolic loops.
  Allocation and acquisition freshness uses this binder too.

A phase contains path conditions, live allocation/value regions, their symbolic
footprints, owned/borrowed acquisition facts, protocol phase, and outstanding
worker/result effects. Each edge specifies preconditions, consumed identities,
produced identities, ownership destination and any transient footprint. Supported
edge kinds have these rules:

| Event | Accounting and synchronization effect |
| --- | --- |
| Allocate/construct | Add fresh storage and check its simultaneous cost, including inputs still alive |
| Replace an owned value | Count old and new storage together whenever their modeled lifetimes overlap |
| Grow a collection | Apply the operation's documented storage effect. A vector push can add an occupied slot and transfer payload ownership. Its private resize adds no charge. |
| Move/send between covered owners | Change destination; no deallocation or second payload charge |
| Acquire | While waiting, retain existing frame/captures; create a fresh acquisition only on an acquiring outcome |
| Release/drop guard | End that acquisition at actual release; surviving allocations move to an unprotected/otherwise justified class and remain charged |
| Spawn | Charge setup/captures before publication; at publication split ownership into worker, completion record and parent handle; child execution may begin immediately, before spawn returns |
| Complete | Drop remaining worker locals in executable order; transfer the result to completion storage, not to free storage |
| Join | Retain caller state while waiting; after completion transfer result and release completion/handle storage |
| Return/break/continue | Execute supported cleanup in its actual order and carry resulting owners to the correct continuation; leaving scope does not discard outstanding workers |

Edges for opaque primitives describe permitted external behavior at their actual
acquisition/release/publication point. They do not make all helper code atomic.
VIR's diagnostic `MemoryEvent` is insufficient as this semantic representation.
The frontend must preserve or recover actual drop order before the memory pass;
if VIR lacks it, add compiler-derived cleanup effects, not guessed last-use drops.

The compiler bridge uses `synchronization::flow::Graph`, a projection of
drop-elaborated MIR with function-local places, fixed field/variant projections,
move/copy/borrow assignments, calls, branches, back edges and actual drop
terminators. An acquiring call carries every possible outcome's executable tag
tests and owned guard projection, including a guard inside a poison error.
Dropping an enclosing result consumes its active owned subtree; dropping a
reference, ending storage or moving a value does not release the owned guard.
Construction/acquisition points are static sites, freshened on each dynamic
visit; neither type identity nor a reused source name identifies a lock.

Exact source-binding spans connect compiler places to VIR bindings. Missing or
ambiguous connections remain unresolved. The bridge also records Verus binding
modes: lifetime-check MIR retains tracked proof code, so its mere presence is not
runtime storage or native exclusion evidence. Tracked witnesses remain available
to the checked custom-protocol interface. This graph describes transport and
cleanup; allocation coverage (04), checked helper substitution (05), protocol
certificates (06) and global bounds (07) must validate their own obligations.
Unknown operations, indirect calls and unsupported projections remain explicit
coverage obligations. A graph's presence alone cannot enable a memory proof.

## Binding allocations to synchronization

At each phase derive an attribution of live storage to active acquisitions or
the unrestricted retained-storage class. Attribution is disjoint for byte summing;
extra known guard conditions may be retained as constraints but cannot subtract
an allocation twice. A protected input payload remains charged through its owner,
not recharged whenever a worker acquires a reference.

To apply a per-holder bound `b`, prove the sum of all simultaneously attributed
storage for that acquisition is at most `b`. Exclusion bounds acquisitions, not
allocations: two buffers under one guard must fit together. Shared views and nested
work under one acquisition contribute to that same sum. At release, every surviving
attributed region must become unrestricted or gain another proved relationship.
One must not conclude it was freed. Reacquisition creates a new interval and
cannot conceal a preceding unprotected overlap.

This local phase rule is stronger than merely labeling an allocation site “under
lock”: it covers its entire live interval, including every helper/exit/transfer.
A buffer born before acquire is unrestricted before acquire; a buffer escaping
unlock remains unrestricted afterward. Both can verify with an adequate total
bound. Storage created during construction or replacement follows the same
lifetime rule. Supported library operations expose the effects defined by the
[source memory accounting rules](accounting/README.md).

## Summary and custom-proof interfaces

A checked summary has the following semantic fields, independent of final Rust
struct names. Add them in focused memory modules; preserve existing summary facts:

| Field | Required meaning |
| --- | --- |
| Binders | Immutable scalar entry snapshots, input ownership regions, instance identities, incoming acquisitions and worker-family parameters |
| Identity relations | Alias equalities and required disjointness, established by caller provenance or proved facts; unknown is never assumed distinct/equal |
| Entry requirements | Needed resource descriptors, supported protocol witnesses and stable predicates |
| Effect graph | All externally relevant phases/edges, simultaneous footprints and transient peaks |
| Exits | Returned/modified owner forests, consumed/released acquisitions, retained shared/result regions and joined descendant obligations |
| Evidence | Source spans, checked lifetime/coverage obligations and trusted primitive/protocol dependencies |

At calls substitute actual binders, preserve alias equivalence classes, freshen
local identities and compose graph edges with caller-live storage. At spawn also
transfer captures and create an asynchronous worker obligation. Never overlay
callee-local storage on caller storage or flatten its acquired/unacquired phases
before combining workers. A scalar `peak(helper)` remains the helper's declared
allowance; its slack cannot establish exclusion or an ownership effect. Refined
summaries must be checked against executable bodies and existing declared bounds.

For a native mutex helper, the guard parameter carries the release duty and its
protected contents have a separate ownership descriptor. A caller binds both to
the actual acquisition before moving the guard. A helper can update the
descriptor, release the guard, or return it to the caller. For
`Option<MutexGuard<_>>`, the `Some` arm resumes the same acquisition and its
contents. The `None` arm carries no guard. All present outcomes must identify
the same acquisition. A helper that returns an allocation on selected exits
retains each exit’s byte charge and original ownership regions. Its caller
selects the returned contents and the remaining mutex contents with the same
branch condition.

A worker may pass its shared mutex to a helper that returns the native lock
result without inspecting the payload. The call binds the actual mutex and
the returned acquisition for that worker and loop visit. The mutex retains the
payload. Its contents enter the worker’s accounting at the first guarded access.
A helper that takes the guard, replaces the payload and unlocks publishes the
entire new allocation tree.

A unit-returning helper can also take the shared mutex itself, acquire it once
and update the protected contents. For example, it can push a box into a vector
and release the guard before returning. The verifier applies the helper’s checked
ownership transformation to the contents at acquisition and publishes the result
at that same guard’s release. This also works through a forwarding helper. A peer
may have changed the vector while the call was waiting, and a later holder may
change it again before the helper returns.

This interface admits a single modified mutex, scalar arguments and a representable
ownership transformation. A skipped write or a poison branch that returns early
preserves the incoming contents. If an original allocation leaves the mutex and
stays live in the helper across unlock, its separate owner needs a lifetime at that
release. Multiple acquisitions inside the helper likewise need separate release
descriptions. The verifier rejects an update when it cannot establish this interface.

For fixed workers with a representable mutex history, a conditional write can
depend on immutable scalar inputs. An arm that skips the write preserves the
incoming contents. The verifier checks each proposed transformation at the
source release and accounts for an extracted allocation through its subsequent
owner and join. Opaque conditions or too many alternatives can prevent a tight
proof. These local checks feed the global interference proof in 07.

When a worker locks a shared mutex in a loop, the incoming contents can be
the initial allocation tree or the result of any preceding release. The verifier
proposes a finite set of symbolic trees, checks the initial contents at publication,
and requires every release to preserve that set. This applies at any iteration
count, including zero. Replacing a vector with a reservation of `b` bytes can
satisfy this obligation. Appending an element on every visit can require a
different invariant. A direct join of an owning result uses the proved alternatives
independently when the order of repeated releases is unknown.

When a worker returns a mutex by value through an indexed handle collection,
the selected join record supplies its producer, ownership tree and reservation.
A buffer removed from that mutex keeps its charge after unlock. This also applies
when another worker drains the collection. A returned shared handle needs a
separate relation to the protected contents of its backing. If that relation is
missing, an indexed join cannot use the constructor site to recover it.

The proof interface in `vstd::resource::holder` identifies an actual witness’s
instance. A `BoundedHolder` implementation must prove the capacity bound for
any finite tracked sequence of **owned** witnesses with the same identity and
capacity. Two references to one witness cannot supply that sequence.
`Incompatible` proves two roles cannot belong to the same instance at once.
The semaphore discharges its population proof by joining its unit tokens.
The vstd RwLock uses its existing unique writer token and shared storage
invariant. It admits multiple readers. Its handles require explicit release.

For custom protocols, expose a verified **synchronization-effect declaration** on
local executable functions, with instance projection, incoming/outgoing tracked
witness projections, acquisition/release outcomes, and an instance holder-bound
predicate. This is a new proof interface to implement in 02/06, not existing
syntax. Macro spelling may be chosen there; its acceptance obligations are fixed:

1. Initialization establishes a protocol invariant and its instance identity.
2. Every witness-producing/consuming executable path refines a declared protocol
   transition. Failed CAS paths cannot produce an acquired witness.
3. The invariant bounds the multiset of outstanding acquisition witnesses, using
   linear tracked state/tokenized state-machine ownership. Ordinary functional
   ensures clauses asserting a count are insufficient.
4. Instance/transition projections agree with executable objects and their checked
   summaries. Private representation and verified transitions prevent outside
   creation of accepted witnesses. Retired/discarded witnesses cannot replenish
   capacity without an actual verified release transition.
5. Local facts used between operations are stable under other workers' permitted
   transitions. Existing invariant masks and single-atomic-operation restrictions
   remain enforced; global population facts cannot be read as thread-local state.

The compiler consumes the resulting checked transition/holder certificate through
the same interface as a trusted mutex contract. Developers prove protocol facts,
not allocation counters. Compiler-generated region descriptors and population
observations are read-only proof inputs. Additional lemmas can prove aggregate
footprint inequalities over them using ordinary Verus assertions and invariants;
they cannot mint identities, alter coverage or declare a byte charge released.
Any new declaration must fail closed until these checks exist. A separate abstract
state-machine proof without the executable transition connection is insufficient.

## Global proof and symbolic composition

The proof obligations are initialization and preservation of coverage, protocol
invariants, ownership conservation, worker-family counts and an envelope `E` over
all permitted interleavings. Each step, including transients, must satisfy
`actual modeled live bytes <= E <= declared bound` for a closed top operation;
helper envelopes compose with incoming caller frames as specified above.
Modular rely/guarantee reasoning uses protocol-preserving interference; it must not assume another worker stands
still while the current helper runs. This is a proof-generation obligation in
06/07, not implicit trust in a local phase graph.

For homogeneous workers with bounded scratch `b`, the same graph/count abstraction
gives `n*b` without constraints, `if n == 0 { 0 } else { b }` under one mutex, and
`min(n,k)*b` under immutable capacity `k`. Distinct phases, shared roots and retained
results are added only at simultaneous states. Heterogeneous workers use explicit
finite sums or proved family envelopes; automatic discovery of arbitrary closed
forms is not required. Use a finite phase abstraction with symbolic multiplicities;
if it loses a necessary correlation, allow a stronger proved invariant/refinement
or report an unproved bound. Never subtract independently maximized peaks.

For fixed workers joined by their publisher, each observation in the publisher
selects its outstanding children by their completion tags. A child contributes
its running phases and its post-cleanup result as alternatives. Delivery moves
that result into the waiting caller’s ledger. A nested worker uses the same rule
at its own spawn and join sites, keeping mutex and permit identities visible to
siblings outside its subtree. A checked helper contributes its caller-relative
profiles, including its full call allowance. Only a guard known to cover an
allowance can constrain that allowance. Addition at a worker site uses immutable
captures or a byte estimate proved against the executable ledger at that site.

For a shared mutex with a checked finite payload history, an unlocked cell can
hold any forest published at a reachable prefix. The global proof charges that
forest while the cell owns it. A worker that has opened the cell while holding
its guard accounts for the contents in its own ledger. At a join, the publisher
can replace a stale cell charge only for identified allocations covered by the
same history. A box pushed into a shared vector therefore stays live after
unlock, with its element slot and owned payload. An incomplete history, an
unexportable worker cost, or a join in another actor can leave the total unproved.

Source budgets retain existing immutable scalar inputs, arithmetic, conditionals,
size queries, local verified numeric spec helpers and declared-peak queries.
Express minimum/maximum with conditionals where needed; no new quantifier or sum
syntax is required in budgets. Internal family sums are mathematical integers,
nonnegative and proved bounded; evaluated source budget arithmetic must still fit
the existing `u64` policy. Counts and allocation-size snapshots follow executable
values and generated loop obligations.

A function-level contract bounds its worker subtree with the existing incoming
caller-frame convention; its composition at a closed top operation bounds the
full operation. A section may contain spawns only if all of its descendants join before section exit; its allowance
composes with all live parent storage. Sections/checkpoints retain existing fixed
bound restrictions. Function/section `current(memory)` and `peak(memory)` inside
a concurrent operation refer to the nearest scope and all its covered descendants,
not a thread-local mutable snapshot. Generate a stable universal phase/count bound
at the checkpoint; precise cross-thread observations require protocol evidence.
Worker contracts describe the worker subtree, with incoming shared provenance
composed by its enclosing operation. Cross-thread references to an ancestor's
checkpoint history are unsupported. Runtime peak queries still evaluate declared
formulas only, with existing expression support and precondition obligations;
they neither query a live scheduler nor infer runtime synchronization state.

On the fixed-worker path, each scoped bound uses the same outstanding tags,
guard identities and shared-payload histories as a whole-function observation.
For a counted family, its erased publication-minus-join count must be zero on
every exit from the section that spawned it. A peak checkpoint selects the
points in its reaching history, including previous loop iterations. A worker's
current observation includes its child phases when pricing shared backing in
its publisher. Inside a worker’s budgeted section, backing that the worker
received before section entry belongs to the enclosing frame. A worker that
needs a peak history opens its own budgeted
section. A source diagnostic can identify the contributing publication and a
guard release in its body.

## Transition review cases

These cases are semantic acceptance requirements and test obligations for 02–08.

| Case | Required consequence |
| --- | --- |
| Allocate under guard, drop buffer, unlock | Scratch stays attributed to that acquisition; exclusion can reduce its combined peak |
| Allocate before lock | The pre-acquire phase includes unrestricted buffer storage for every waiting worker |
| Unlock before buffer drop | Surviving buffer remains unrestricted while another acquisition may allocate |
| Two aliases of one lock | Same instance; helper/capture substitution preserves exclusion |
| Two separate locks of one type | No common exclusion; permitted simultaneous buffers sum |
| Unlock then reacquire | Two acquisition IDs; the unprotected gap remains in the graph |
| Several buffers under one guard | Their simultaneous sum must satisfy the single per-holder bound |
| Borrow/share the guard into supported work | Same acquisition; no duplicate allowance; illegal Send remains rejected |
| Return/move buffer through helper | Same allocation ID; exit descriptor retains its charge even after release |
| Complete worker before join | Completion cell and result remain live; parent and other workers can overlap them |
| Replace lock-protected owning payload | Count distinct payloads while both are live and update the shared root once |
| Fail try-acquire | No acquisition witness; already-live storage remains |

## Implementation ownership

02 implements contract recognition, identities, cleanup effects, layouts and the
custom declaration schema. 03.1–03.4 implement selected threads, semantic closure
invocation, strong Arc, completion records, nested/spawn-loop population and
rejection boundaries. 03.2 owns the checked worker-summary foundation and join
Result handling; these cannot wait for 05. 04 implements phase attribution,
escapes, cleanup and transient lifetime obligations. 05 extends the common summary
interface for general helpers, owning protected payloads, guard returns and
lock/try-lock Result operations. 06 implements certificate checks, custom protocol
integration, the verified semaphore and RwLock surface. 07 implements global
interference/count proof generation, composition, sections/checkpoints and query
compatibility. 08 audits coverage, trust, rejection behavior and user documentation.

The source integration points remain
[pipeline](../../source/rust_verify/src/resource/memory/pipeline.rs),
[identity recognition](../../source/rust_verify/src/resource/memory/intrinsics.rs),
[ownership summaries](../../source/vir/src/resource/memory/summary.rs),
[accounting](../../source/vir/src/resource/memory/accounting.rs) and
[proof generation](../../source/vir/src/resource/memory/symbolic.rs).
New opaque layouts require a model-version change and matching static/runtime size
semantics; TODOs 02/07 own these changes. No existing concurrency capability is
claimed by completing this specification.
