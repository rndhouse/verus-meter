# Memory contracts

Verus Meter proves upper bounds on peak memory for a supported subset of Rust.
Use the [executable examples](../examples/resource/memory/README.md) to learn
contract syntax, heap ownership, loops, and expected failures.

## Contracts and queries

- `resources peak(memory) <= bound` limits the maximum memory live at once in a
  function or budgeted section. Functions without a resource clause receive only
  ordinary Verus verification.
- `value_size(T)` measures inline storage, excluding separate allocations;
  `ref_size(&T)` measures a reference, excluding its pointee. Both also accept
  binding names.
- `return_size(helper)` measures the inline size of one result using the named
  function's declared return type. The function needs no resource contract.
  For example, a `u16` result takes two bytes and a `Vec<u16>` result counts
  the vector handle. The query never calls the helper.
- `peak(helper(arguments))` queries the helper's declared allowance for those
  arguments, without executing it. `peak(helper)` takes its maximum allowance.
- `assert(peak(memory) <= bound)` checks the peak so far;
  `assert(current(memory) <= bound)` checks storage still live. Both refer to the
  nearest budgeted section or function.

Function budgets can depend on immutable scalar inputs and use arithmetic,
conditionals, and local verified numeric specification functions. Budget
arithmetic must fit in `u64`. Sections can also use executable locals and the
length of a named slice or vector. For example, a section can declare
`packed.len() * return_size(checksum) + peak(checksum)`. Each entry takes a
fresh snapshot of its allowance. The enclosing scope pays that allowance
alongside its own live storage. Checkpoints still require fixed bounds.

A vector created outside a section can grow inside it. The section
pays for each replacement while the vector's owner retains its buffer on exit.
A push that fits the existing capacity adds no backing charge. If the section
replaces a buffer it allocated earlier, both buffers count at replacement.
See [contract examples](../examples/resource/memory/README.md#contracts).

## Runtime queries (prototype)

`#[queryable_peak_memory]` exposes a nongeneric free function's allowance through
`function_name::peak_memory_bound(arguments)`. Queries support unsigned scalar and
Boolean parameters, constants, addition, multiplication, comparisons, Boolean
operators, conditionals, supported model-size types, and local spec helpers in the
same `verus!` item scope. Argument-specific `peak(helper(arguments))` queries use
the callee's declared allowance. Runtime queries return model bytes
as `Result<ModelBytes, QueryError>` using exact arbitrary-precision arithmetic.
Use `fits_within(budget)` to compare with a `u64` budget or `to_u64()` for an
explicit conversion that fails if the allowance is too large. Negative results
are errors; results above `u64` remain representable. Existing verification of
the target function still enforces its resource arithmetic constraints.
The runtime interprets retained expression data; the query implementation is
tested Rust tooling, not formally verified. The caller must still establish the
function's execution preconditions. Unsupported queried bodies fail compilation;
unannotated resource contracts retain their existing supported scope.
The query namespace follows the function's visibility and configuration. A
prepared standalone verifier discovers its runtime bundle automatically; Cargo
clients declare the runtime dependency explicitly. Querying does not enforce
execution preconditions or override verification bypass flags.
Compare an allowance with an explicit model-byte budget before calling the target,
after establishing its execution preconditions separately. An allowance exceeding
the budget does not prove that execution cannot fit. Query and caller costs are
separate; OS RAM discovery and reservation remain future work.
See the [example and run instructions](../source/verus-meter/runtime/README.md#run-the-example).

## What the guarantee covers

The model calculates storage sizes for source values and separately owned
allocations assuming a 64-bit target. It does not measure the compiled program's
physical stack, allocator overhead, fragmentation, or resident memory. Struct
sizes add their fields without ABI padding; ghost and proof state contribute no
runtime storage.

- Parameters, local slots, owning handles, and modeled temporaries count while
  live. Moves transfer ownership; copies require additional storage. Scope exit
  and explicit drop release storage; last use alone does not.
- Short-circuit operands follow the same ownership restrictions as explicit
  branches. Moving or dropping an enclosing heap owner in a conditional operand
  is rejected; allocations local to the operand remain supported.
- An owning `Option` match must bind each present owner to move it. Wildcards
  over owning values are unsupported because ignoring a value does not drop it;
  a named binding such as `Some(_value)` establishes an ordinary value lifetime.
- Heap backing counts even when a collection's logical length is smaller than
  its capacity. Child allocations count separately from their handles.
- Reallocation and replacement include overlapping old and new storage. Vector
  growth follows the model's allocation policy, not a system-allocator guarantee.
- Calls compose the callee's declared budget with caller storage that remains
  live, including retained incoming allocations. Declared slack still counts.
- Loop iterations can reuse released storage; retained allocations accumulate.
  Generated resource invariants must be proved at entry and on back edges.
  Ordinary Verus correctness, bounds, and overflow obligations still apply.

A byte bound and an ownership description serve different purposes. The checker
preserves child identity, order, capacity facts, and input lifetimes across
supported operations. Missing ownership support is an error, even with a generous
budget; ordinary proved byte upper bounds remain valid.

When a required ownership summary cannot be inferred, diagnostics identify the
failed inference boundary and, where available, the executable operation or loop.
This is an unsupported transformation, distinct from a byte-bound proof failure
or a solver resource limit. Optional summaries may remain absent.
Generated loop failures also label the memory property being checked, such as
worker membership, backing storage or ownership conservation. Verus retains the
check location: entry, back edge, continue or loop exit.

## Supported boundary

Supported building blocks include native integers, fixed integer arrays,
concrete nongeneric structs, `Option`, `Box<T>`, `Vec<T>`, and `Box<[T]>` with
supported layouts and operations. Nested ownership composes through fixed fields
and runtime collections. Checked calls currently require safe, nongeneric,
verified functions in the same crate and an acyclic call graph.

Supported loops include counted while/unconditional loops, representable exits,
finite half-open integer ranges with supported `rev`, `skip`, and `take` adapters,
and forward loops over shared slices and vectors. Borrowed loops charge the
iterator and yielded reference while the source owner retains its storage.
Forward loops can also consume standard vectors. The iterator retains the
original backing allocation until it is dropped, even if no items remain.
Each successful advance transfers one element to the loop body. When elements
own allocations, the iterator requires a complete, precise ownership forest
without outstanding shared references or caller-owned regions. On exhaustion
or an early exit, it releases any unvisited elements along with its backing.
For consuming loops, an `if` over supported immutable scalars in scope at
loop entry can reserve temporary storage only on the branch that uses it.
Exact ownership summaries support selected conditional effects, child
transfers, and indexed updates. This does not cover arbitrary data-dependent
progress, partial exits, or all iterator APIs. A local peak proof can succeed
while exporting caller-visible ownership remains unsupported.

Other owning containers, shared ownership, custom destructors, recursion,
generic layouts, and cross-crate resource summaries remain unsupported. Examples
illustrate supported programs rather than promise every operation on their types.
See [heap and loop examples](../examples/resource/memory/README.md#heap).

Internally, charges distinguish `host.local` and `host.heap`. Current source
contracts bound total `memory`; separate kind-specific limits and GPU allocator
models are not yet provided.

### Allocation sizes across calls

A vector reservation records the capacity at the allocation site. Moving the
vector carries that backing charge, and a growing push updates it under the
model's allocation policy. A helper returning two buffers with capacities
selected by the same flag can preserve both selections through a forwarding
call. A caller can prove their combined charge for either flag and the
individual charge after extracting one buffer.

For a counted loop that only updates local observations, the checker can infer
the final value of a scalar or shared slice length overwritten on every
continuing path. The initial value applies on zero visits. On positive counts,
the final write may depend on input observations and the last visit's index.
The checker proves this relation at the loop head and checks the completed
count on exit. This rule covers non-nested loops comparing scalar locals or
literals with checked progress. A condition with writes or a partial break
requires separate exit reasoning.

A verified helper can also supply an exact scalar result through a
`returns` clause or an unconditional `ensures` equality. Supported right-hand
sides include scalar arguments, shared slice lengths, arithmetic, comparisons,
and conditionals. When a required allocation size still depends on an
unresolved observation, the diagnostic identifies the dependent allocation
and the loop or helper call where inference lost the relationship.

## Synchronization size queries

The `source-values-v40-64` model supports type-only sizes for standard `Mutex<T>`,
`MutexGuard<T>`, poison/try-lock wrappers and `Result<T, E>` with supported concrete
payload layouts. A mutex occupies nine source-state bytes plus its inline payload;
a guard occupies an eight-byte reference. A poison wrapper occupies its payload,
and a variant stores one tag byte plus its largest inline payload. Separately
owned allocations remain separate from these inline sizes. Static and runtime
queries use the same policy, which does not describe OS lock storage or ABI layout.

Strong `Arc<T>` and standard/vstd thread join handles occupy eight source bytes
each. An Arc's separate backing costs sixteen control bytes plus its inline
payload; separately owned payload allocations retain their own charges. Thread
completion storage has a one-byte state tag and retains the inline result once
produced. A native join error has a sixteen-byte opaque handle, so
`value_size(std::thread::Result<u64>)` is seventeen bytes. This inline size does
not provide an allocation bound for arbitrary panic payloads. Executable closure
storage is the sum of its captures after proof erasure, excluding separately
owned descendants. These rules follow the
[concurrent storage policy](verus-meter/concurrent-model.md#library-trust-and-source-storage-policy).

Resource-contracted code supports constructing and dropping concrete `move`
closures with supported executable capture layouts. Moved captures retain their
allocations; partial captures transfer only the selected owners, while the
enclosing inline slot remains live. Copy captures create inline storage. The
analysis derives closure Copy behavior from the surviving executable fields,
including nested closures: erased tracked state cannot hide runtime copies.
Creating a closure does not execute its body. General closure invocation,
capture summaries across function interfaces and closure `value_size` queries
remain unsupported.
Scalar captures, supported inline scalar projections and owned collection geometry
are observed at construction; moving or copying the closure preserves those
observations. Repeated constructions bind their observations to the executing
source-loop occurrence. Supported retained-worker collections preserve each
construction's observations across iterations and partial collection.

Worker invocation evidence describes the original body's owned or borrowed
environment and its cleanup responsibility, without inspecting a generated FnOnce
wrapper. A borrowed body returning leaves its captured owners live until the
consuming invocation cleans them up; an owned body must account for each capture
through its moves and drops. Returned owners stay separate from environment cleanup.
Implicit capture destruction order is unspecified by
[Rust's source rules](https://doc.rust-lang.org/reference/destructors.html#destructors.operation);
capture indices cannot justify a synchronization release order. Original body
cleanup and unwind edges remain proof obligations.

Concrete standard/vstd workers undergo the ordinary symbolic body analysis,
including supported helpers, branches, loops and capture cleanup. Their summaries
retain ordered source effects, ownership templates, construction inputs and
compiler synchronization identities. Each worker has independent allocation proof
state and history. Publication transfers existing captures; completion retains
the body-derived result; join transfers it once while retaining the waiting frame.
Shared links keep their canonical backing identity. Implicit capture cleanup is
recorded as an unordered group at each source exit.

Each publication records the caller's live storage before and after the capture
transfer. The child may enter, run or complete while the caller is still inside
`spawn`. For an independent body using reviewed local operations, the local
analysis checks early completion against the caller's live frame. For straight-line
independent bodies it also checks fixed-size temporaries before they drop. It uses
the checked result descriptor when its owned bytes can be expressed at the
publication site. For other bodies the worker's execution graph retains the
conditional overlap for the interference proof.

A join records the waiting caller's footprint, the point where its handle and
the completed result coexist, and the footprint after it receives the result.
The completion record holds the inline payload and its tag. Owned buffers keep
their allocation identities across the transfer. Each observation belongs to
the executing actor and its source operation in the synchronization graph.
A helper receiving an input handle keeps the same wait phases with its formal
operand. Its result can still take either outcome.

A worker can spawn and join children or receive an existing join handle in its
captures. Handle transfer moves responsibility for the target's completion record
and imported shared references; it executes neither a join nor a strong destructor.
Nested actors have separate loop contexts. Spawn/join loops retain parent and
local occurrence coordinates. For supported retained collections, exact
membership invariants describe the outstanding occurrences at each back edge;
selecting a handle preserves its own inputs and conditional result description.
Selections can name several compatible checked body families, while retaining
the selected occurrence's own result description. Local proofs cover finite
mixed-family collections, separate symbolic collections and supported symbolic
batches containing several worker families per iteration, including partial joins
within a batch. Shared captures/results still need further population support.
Retained scalar results preserve checked body expressions through `join().unwrap()` and explicit `Ok`/`Err` matches,
including Boolean and signed values. They can supply allocation sizes directly or
through supported helpers after partial collection. Scalar inference requires a
description from every possible checked body; an unknown result cannot borrow
another family's value. Existing expression and functional-proof requirements
still apply; these descriptions add no assumptions about source scalar values.
Other loops require the outstanding-worker state to match at the back edge.
A worker can also capture a handle popped from a supported population and join
it. The outer join can recover the resulting scalar or buffer size through the
collecting worker's summary. A worker can also take ownership of the whole
vector and drain it. In supported loops the publishing worker supplies the
description of the captured collection, and the receiving worker proves its
remaining length and membership after each pop. Dropping a collection with an
outstanding handle fails the local proof. A worker may return the remaining
vector to another thread that owns its join handle. The receiving thread
uses the snapshot taken when that worker was spawned, including which
workers its result contains. Its local checks cover the returned vector's
backing, the remaining joins, and the selected workers' result storage.

An ordinary helper can take one handle vector by value and return the same
backing. Its caller keeps the identities and join obligations of the surviving
workers. A helper can pop and join vstd handles down to a symbolic remaining
length when it can dispose of either outcome (a scalar or unit on success and
unit on failure). Native handles and handles with owning result payloads can
pass through a helper intact. The handle type alone supplies no proof that an
incoming worker succeeded. These are local ownership and byte checks. The
global concurrency proof is still required.

When workers capture clones of a coordinator's `Arc`, the local analysis can
reserve one backing allocation across a symbolic number of outstanding workers.
A single allocation created before the publishing loop stays charged once. Its charge
includes locally owned payload storage. For example, workers sharing an `Arc<Vec<u8>>`
retain one control block, one inline vector and one buffer at its reserved capacity.
If the last fixed strong handle moves into
a worker whose handle enters a collection, the outstanding workers retain the
backing. When a push evaluates a spawn directly, the slot records the handle
produced by that spawn. Each join reconciles the aliases captured by that worker.
When capture counts differ within one vector, each allocation's count is the
sum over the occupied slots of the references captured by that slot's worker
family. A pop transfers a handle out of the vector. Joining its worker and
dropping the returned alias are separate accounting events. A drain can stop
with a live handle or branch on the remaining length when both paths consume
the same ordered slots.
If workers can return different roots, the coordinator checks the selected
result's allocation identity at the join. Moves and local clones preserve that
identity, and the last local drop releases the result's claim on the backing.
A fixed worker can receive that alias, or an individual popped handle whose
worker returns a captured `Arc`. It may move, clone, drop or return the alias.
The publisher retains the backing through the transfer and reconciles the
receiver's checked entry and exit references when it joins the receiver.
The publisher can store results of successive visits to the same join in a
vector. Each occupied slot retains the allocation selected on its own visit.
Popping the slot transfers that reference, and dropping the vector releases
the references in its remaining slots. Local clones may survive either event.
A worker receiving an entire vector of handles cannot drain indexed shared
claims owned by its publisher. That transfer needs a summary of the references
the receiving worker consumes or returns.

For an allocation created before the publishing loop, a returned `Arc` can
retain the original ownership of its payload through handle and result vectors.
An incoming buffer stays charged to the caller. When a helper consumes it, joins
all its workers and returns unit with the payload destroyed, the caller can reuse
the bytes on return. The caller allows for its buffer throughout the helper's
declared budget. Local lifetime evidence and the pending global peak obligation
travel separately.

Two fields of one payload can refer to the same inner allocation. The last outer
drop releases both references. Any surviving inner clone keeps that allocation
charged. The publisher can retain a whole payload conservatively until it proves
that the outstanding handles and stored results have relinquished it. A worker
checkpoint also considers nested allocations retained by indexed peers.

An embedded join handle keeps its original worker and result storage. For an
identified allocation with a proved sole remaining strong handle,
`Arc::into_inner` moves out its payload. An explicit `Some`/`None` match can join
the recovered handle. Losing the handle on destruction reports a detached worker.
These checks preserve the ordinary Rust outcome specification. Extracting from
an allocation with unresolved aliases requires additional evidence.

A fresh `Arc<Vec<u8>>` created on each loop visit keeps that visit's identity
through capture, handle-vector storage and join. With `n` visits and capacity
`b`, the buffers can contribute `n * b` bytes. Several workers from one visit
share its single buffer. The analysis accounts separately for each control
block, inline vector, handle slot and completion tag. Per-visit byte transport
requires a completely owned payload without nested strong or worker handles.
A fixed canonical payload can retain those handles with their original identity.

When workers from one visit retain aliases independently, one handle carries the
backing charge. A peer's join can transfer its reservation to a returned alias.
Either returned alias can drop first when the charge can pass to a live result
with the same allocation identity. The verifier also accepts evidence that the
peer reservations have all ended. A drop that would leave the backing with an
uncollected peer needs evidence of where the charge will remain. Forwarding a
returned alias with these reservations to another actor requires further support.
The global concurrent peak proof is still required.

At a worker's `current(memory)` checkpoint the verifier can reconcile directly
identified strong handles with the publisher's ownership at spawn. A worker
that joins a peer can use the peer's actual result to establish how many handles
survived. When the last handle drops, fixed fields in the shared payload release
their handles in turn. Multiple paths to the same allocation pay for it once.
A publisher or sibling that can still hold an alias keeps the backing live in
this check. The publisher's own continuation can still keep the backing charged
until collection. If a captured handle came from a collection of workers that
return different allocations, the check uses the identity frozen at that join.
Dropping its last clone in the child releases exactly the selected reservation
in the checkpoint view. Any other result or slot naming that allocation still
retains its backing.

The publisher checks backing sizes against its allocation state. A constant
allowance proved there can be used at the worker's source checkpoint. Symbolic
components from a single proof scope are checked where their variables are in
scope. Publisher-side checks preserve branch conditions over immutable scalar
captures. Other conditions can conservatively include a worker phase. General
combinations of independently symbolic frames and backing costs need a
relation between their scopes.

The proof boundary separates construction, transport and byte accounting.
Generated builders establish worker-description properties; verified one-step
collection laws preserve those descriptions without reopening them. Loop exits
and membership invariants use the same ownership transformation, with a separate
checked inequality for backing storage. Worker data is an opaque specification
value, opened only by worker queries, so ordinary allocation proofs do not expand
its recursive descriptions. Descriptions do not assert completion
or charge future results as already live. Explicit and lexical destruction must
prove that no outstanding worker remains in a discarded collection.

For these checked workers, join-result matching and `unwrap` use the successful
normal-execution outcome, conditional on Verus checking every possible body/helper
obligations and on the model's environmental assumptions. The original functional
join call and its postconditions remain. An ordinary `Result` or an external
functional specification cannot supply this evidence. Outgoing allocation facts
must close over construction observations or a checked ownership template;
body-local proof variables cannot escape through a result.

For fixed workers, publication checks the combined strong handles claimed by
outstanding siblings. Transferring a join handle moves its existing claim to the
receiving worker. Completion checks that each surviving strong handle is reachable
from the result through acyclic shared payloads. Imported backing stays in the
enclosing domain until the worker's reference changes are composed there.

Supported sequential paths now account for standard strong `Arc` construction,
cloning, readonly payload access and explicit/implicit destruction. Backing and
owned payload storage remain charged until the last strong release. Copies of
analysis state do not create handles. Nested clone receivers retain their owned
temporary storage through rustc's destruction scope, including later operands;
unresolved scopes reject. General imported populations and outgoing shared
owner trees still require additional concurrent interfaces.
Executable effects require exact compiler call bindings in the correct body;
ghost arguments and unexecuted closure bodies do not create memory events.

Primitive identification uses compiler definitions, including through aliases.
Compiler-derived synchronization graphs preserve moves, acquisition outcomes and
actual guard cleanup. Runtime synchronization values still reject in
resource-contracted code until concurrent allocation coverage and bound checking
are connected. Native functional specifications assume neither acquisition
success nor a protected payload invariant. The
[concurrent TODOs](verus-meter/todo/concurrent/README.md) track the remaining requirements.
Worker-local obligations are checked, but a required global diagnostic still
rejects every concurrent memory contract and prevents exporting it. These local
checks are necessary inequalities, not a sum of thread peaks or a simultaneous
memory theorem. General population and handle/helper interfaces, global
shared-lifetime composition, synchronization containment and the simultaneous
envelope still require the remaining concurrent interfaces.
Detaching a worker is rejected.

## Concurrent extension specification

The [concurrent semantics](verus-meter/concurrent-model.md) define the required core scope,
synchronization effects, ownership rules and proof interfaces for the planned
extension. They include standard primitive contracts and custom Verus protocols.
This specification does not enable concurrent memory checking; implementation
progress is tracked in the [numbered TODOs](verus-meter/todo/concurrent/README.md).
