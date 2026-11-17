# Verus Meter: heap support, loops, and remaining blind spots

Research handoff, prepared 12 November 2026 from `main` at
`00877808810c85e76c4360c82bbb48479307f432`.
The accounting model identifies itself as `source-values-v38-64`.
This describes the implementation and its documented boundaries; it is not an
independent soundness audit or a claim of support for arbitrary Rust programs.

## 1. Purpose and current position

Verus Meter extends Verus with source-level peak-memory contracts. The goal is to
prove that supported code stays within a declared memory allowance, including
temporary allocation overlap and storage retained across calls and iterations.
The heap-loop work items 01–08 are complete within their stated acceptance
boundaries. This provides a shared model for supported while loops, unconditional
loops, and finite scalar for loops, rather than a separate accounting engine for
each syntax form. It does not provide comprehensive iterator or heap API support.

The main abstraction is compositional ownership: inline values, separately owned
allocation trees, runtime collections of child trees, and operations transforming
those trees. We want to extend classes of programs through these abstractions,
not add a special rule for each spelling of a nested container type.

The user-facing contract is `resources peak(memory) <= bound`. Functions without
this clause receive ordinary Verus verification only. The analysis generates
ordinary proof obligations; normal Rust/Verus bounds, overflow, and logical
correctness checks still apply.

Primary references: [memory model](../../../../model.md),
[analysis implementation](../../../../../source/vir/src/resource/memory/mod.rs), and
[completed heap-loop work](README.md).

## 2. What “memory” means here

This is a source-value model with a fixed 64-bit size policy, not a measurement
of the compiled program's physical stack, allocator usage, resident memory, or
GPU memory. Native integer widths determine their modeled sizes; `usize` and
`isize` use eight bytes. Struct layouts add executable fields without ABI
padding. Ghost/proof state contributes no runtime storage. `Option<T>` uses a
modeled tag and payload rather than Rust's niche optimizations.

Parameters, local slots, temporaries, iterator state, and owning handles count
alongside heap allocations. A move transfers ownership; a copy creates another
value charge. Scope exit or explicit drop releases storage; last use alone does
not. A reference does not acquire its pointee's allocation charge. The distinction
between current live memory and peak memory matters: dropping storage lowers
current usage but cannot erase an earlier peak.

`value_size(T)` measures inline storage, excluding separate allocations.
`ref_size(&T)` measures the reference, excluding borrowed data. Neither is Rust's
physical `size_of` guarantee. Budgets can use symbolic inputs, arithmetic,
conditionals, local numeric specification functions, and declared helper budgets.
Formula results and arithmetic must fit in `u64`. Sections and checkpoints
currently require fixed bounds.

### Memory kinds

Internally, every charge has an extensible namespaced kind: `host.local` for
inline values/handles and `host.heap` for separate owned allocations. Placement
determines the kind. A box handle stored inside a heap object is itself part of
that heap object's inline payload.

The accounting core can select individual kinds or sets of kinds. It preserves
simultaneous usage, selecting kinds at each point before taking a maximum;
independent per-kind peaks must not simply be added together. However, source
contracts currently expose only total `memory`. There is no source syntax for
separate heap/RAM/VRAM limits, and there are no GPU allocation rules. Naming a
future kind such as `device.0.vram` is possible; sound allocation, transfer,
overlap, and release semantics still need implementation.

## 3. Supported heap ownership and operations

These are supported building blocks, subject to the operation, control-flow,
and inference restrictions below. A representable type alone does not imply
every operation on it is supported.

| Class | Current support |
| --- | --- |
| Fixed owned allocation | `Box<T>` for supported layouts: an eight-byte handle plus separately charged payload storage. |
| Resizable allocation | `Vec<T>`: a 24-byte handle, capacity-sized backing, and separately tracked allocations owned by elements. Empty length does not imply empty backing. |
| Runtime-sized fixed allocation | `Box<[T]>`: a 16-byte handle and length-sized backing, plus child allocations where present. |
| Fixed ownership composition | Concrete nongeneric structs, box contents, supported owning `Option<T>`, and nested combinations of these layouts. |
| Runtime ownership composition | Collections of child ownership trees, preserving each child's descriptors, order, reservations, and original-input provenance. |

Fixed child edges and runtime child collections compose recursively. This is the
general mechanism needed for nested owners: there is no separate model for every
combination of vectors, boxes, slices, and fields.

Supported operations include construction, whole-owner moves, lexical and
explicit drop, helper consumption and return, and supported shared/mutable
borrows. Fixed-field extraction and replacement preserve unaffected siblings.
Partial moves retain the parent's inline slot. Replacement evaluates the new
value while the old allocation remains live, then releases the displaced subtree.

For collections, the model supports insertion, indexed borrowing and updates,
supported growth and replacement of selected owning children, and owning
`pop`/`remove`. Removal transfers the complete child tree and reindexes the
remaining metadata. Insertion transfers a child's allocations rather than
charging them a second time. Growing parent backing overlaps old/new element
slots but does not duplicate allocations owned by those elements. Dropping a
collection releases its backing and attached children; previously extracted
children have independent lifetimes.

### Capacity and allocation overlap

Peak heap usage depends on reserved capacity, not just logical length. The model
keeps capacity/reservation lower bounds separate from charged-byte upper bounds;
these are different facts. There is no user-facing `mem_capacity` annotation.
Supported facts are inferred and checked within helpers and at their call sites.

Vector growth follows an explicit source-model policy:

`new_capacity = max(minimum, 2 * old_capacity, length + 1)`

The minimum is eight elements for one-byte elements, four for elements up to
1,024 modeled bytes, and one for larger elements. Zero-sized elements do not add
backing bytes. Reallocation charges old and new backing simultaneously at the
peak. This is an abstract policy, not a promise about the system allocator.
When only a reservation minimum is known, possible growth must still be covered.

Converting a named vector with `into_boxed_slice()` is modeled as a length-sized
replacement allocation overlapping the old backing, even if a real allocator
could reuse storage. Other boxed-slice construction/conversion APIs are not
automatically supported by this rule.

### Calls and incoming ownership

A checked call composes the callee's declared allowance with caller storage that
remains live. Declared slack still counts; `peak(helper)` is a contract query,
not an inferred measurement of the current helper body.

Call summaries distinguish three things:

1. The complete ownership forest, including caller-originated allocations.
2. New storage charged inside this function's frame.
3. Original-input lifetime regions that must be partitioned or retained.

Owned inputs can split into independently released or returned subtrees.
Borrowed incoming allocations remain charged to the caller throughout the call;
final replacement effects are installed afterward. The helper's zero local
charge for an incoming child does not mean the child is absent or has zero
capacity. Precise descriptors survive helper delegation and later caller-side
indexing, extraction, growth, and drop.

Unknown ownership information is an error, even with a generous budget. There is
no fallback that replaces a missing child forest with a parent byte total.
Ordinary proved byte upper bounds remain valid: for example, some fresh returned
runtime extents use the producer's verified budget as a byte ceiling while
retaining ownership structure. Such bounds can overcharge callers without
discarding child identity or inventing capacity facts.

## 4. Heap support inside loops

Local accounting and exported ownership summaries consume shared checked loop
records. Summaries derive effects from accepted operations rather than matching
source method names independently. Generated invariants are obligations proved
at entry and back edges, not assumptions granting the requested resource bound.

| Area | Supported subset |
| --- | --- |
| Ordered effects | Multiple appends/removals, whole-child transfers, child transformations, precise helper calls, and completed nested loops. Persistent collections can occupy different fixed fields of an owner. |
| Nonuniform children | Each generated/transformed child retains its own nested footprint and reservations. Supported affine costs can be summed symbolically without unrolling the count. |
| Evolving collections | Exact ordered recurrences for revisiting children, indexed updates/replacement, removal with shifting indices, and pop/change/restore. Untouched subtrees retain their metadata. |
| Conditional work | Stable scalar flags and affine counter comparisons with stable thresholds, combined with Boolean operators. Exact ordered visit intervals select complete effect programs. |
| Progress/counts | Strict/inclusive comparisons in either direction, literal strides, countdowns, supported length changes and partial final removal blocks, and moving operands whose relative gap closes by a positive constant. |
| Carried scalar state | Supported constant additive translations retain exact exit values. Allocation quantities can use supported arithmetic, stable observations, and translated counters. |
| Nested work | Supported inner counts and allocation sizes can depend on outer scalar state. Completed inner transformations compose with outer effects. |

Zero visits preserve entry state. Partial traversals preserve unconsumed children
and backing. Ordered transfers preserve distinct capacities and extraction order,
including reversal where last-element extraction requires it. Every intermediate
allocation peak remains checked, not merely the final retained footprint.

Some recurrence classes expose closed forests through checked base/successor
equations and induction, including stationary overwrites and affine descriptor
updates. Other classes retain an exact recurrence representation but have limited
automatic cost and indexed-view reasoning. An exact representation does not
guarantee that the solver can prove every useful bound about it.

### Loop syntax, exits, and cleanup

Supported while loops and unconditional loops reuse the same accounting rules.
`break`, `continue`, and `return` release the scopes they leave while retaining
escaping ownership and peak history. Nested and labelled exits and memory-section
cleanup have checked paths. Loops without a local back edge preserve their actual
entry state and can support value-producing breaks.

Reusable counted summaries admit representable head breaks, including effect-free
inequalities refining the controlling comparison. Supported continuations can
skip selected work but must still establish the visit's checked progress. Facts
valid only after a complete iteration cannot be exported after a partial visit.

There are two separate acceptance gates: proving the local peak and producing an
exact caller-visible ownership transformation. Cleanup may be correct and a local
bound provable while the function's runtime ownership interface is unsupported.
Different return paths need compatible ownership proof states and descriptors;
a byte total alone cannot reconcile unrelated returned collection states.

### For loops and iterators

Supported for loops traverse finite half-open native integer ranges, including
signed ranges and aliases/named iterators, with standard `rev`, `skip`, and `take`
compositions where Rust/Verus support them. Iterator factories can preserve this
scalar state through checked calls. Successful visits and exhaustion integrate
with existing Verus lowering and the same checked heap effects used by while.

Iterator storage counts: a range stores two bounds; `skip` and `take` each add
one `usize`; reversal adds no fields. The Verus wrapper's ghost index/history do
not add runtime bytes. Setup, evaluation order, advancement results, and yielded
bindings still matter to peak overlap. Standard generated iterator invariants
remain required, and factory callers may need logical postconditions establishing
the count.

This supports scalar for loops that construct or transform heap owners. It does
not yet support iterating over borrowed or owned collection elements through
their iterator APIs.

## 5. Explicit gaps and blind spots

### A. Unmodeled language, ownership, and library features

- Other owning container classes, such as reference-counted owners, strings,
  maps/sets, and deques, do not inherit support from vectors. Shared ownership
  needs release rules based on the last owner.
- Generic checked functions/layouts, recursive structures/calls, custom
  destructors, executable enums other than supported `Option`, owning array
  elements, closures, and cross-crate checked calls remain outside the subset.
  Structs containing reference or ghost/tracked fields are also excluded.
- Inclusive ranges, borrowed/mutable element iterators, owning `into_iter`,
  other adapters, and custom iterator classes lack the required models.
  Unknown iterators never inherit scalar ranges' zero-heap behavior.
- Physical layout/padding, allocator metadata and fragmentation, actual allocator
  reuse, optimized binary lifetimes, device memory, and concurrent/shared
  allocation behavior are not covered by the current source model.

### B. Representable layouts with unsupported operations or control flow

- Whole-owner reassignment/replacement through `&mut Vec`, stored reference
  aliases carrying allocation effects, owning-vector slice views, direct moves
  out of borrowed owners, and temporary-container extraction have restrictions.
  Supported fixed-child replacement and explicit pop/remove transfers do not
  imply support for these broader forms.
- Incoming extraction/replacement is restricted in protected ordinary branches
  and memory sections. An enclosing collection cannot acquire child allocations
  inside a separately budgeted section. Direct escaping result moves have
  specific support; that does not permit arbitrary release of enclosing owners
  while spending the section's independent allowance.
- Reusable loops with value-producing breaks, unrepresentable stopping counts,
  and partial exits changing fixed ownership roles or original-input regions
  cannot export general exact summaries. Exits inside operands or call arguments
  are unsupported.
- Payload-dependent decisions, nonlinear counter predicates, nontranslation
  progress, and some saturation-dependent length comparisons remain unsupported.
  Correlations between separate decisions are not generally solved to recover an
  otherwise incompatible ownership program.

### C. Inference, modularity, and proof automation limits

- Reservation, cardinality, and scalar-state inference covers specific checked
  relations, not arbitrary arithmetic invariants. Resource summaries do not
  automatically provide every functional length/content postcondition needed by
  ordinary Verus proofs.
- General cost/view induction for evolving forest recurrences remains limited.
  A larger allowance cannot compensate for missing ownership metadata or an
  unrepresentable transformation. A supported representation can also need
  stronger user invariants or exceed practical solver resources.
- Fresh runtime outputs and iterator state must close over supported scalar
  observations or have a supported producing summary. Not every locally derived
  mutable quantity can be transported across a call.
- Symbolic guard expansion explicitly rejects more than six distinct decisions
  or sixteen threshold boundaries. Live ownership alternatives are capped at
  1,024. These are implementation complexity limits, not semantic memory bounds.
- Interface consistency checks compare supported result/borrowed-effect shapes;
  they do not establish equivalence of arbitrary complete forest expressions.
  The compiler analysis, adapter policies, checked-record extraction, and their
  correspondence to generated obligations remain important assurance boundaries.

These categories should stay distinct: a deliberately abstract allocator policy,
an unsupported program, a failed proof, and an implementation bug are different
outcomes.

## 6. Questions for further research

The following are investigation questions, not claims of implemented support or
an agreed implementation plan.

1. **Iterator ownership and lifetimes:** What reusable state/effect interface can
   express borrowed, mutable, and consuming traversals, including remaining
   backing, yielded children, early exit/drop, and adapter composition?
2. **Stopping and progress:** How can exact partial traversal summaries cover
   richer data-dependent stopping and piecewise/nonlinear progress without a
   separate source-pattern rule for each loop?
3. **Forest transformations and proofs:** Which algebra and induction interface
   gives scalable cost, indexed-view, and reservation reasoning for overlapping
   updates and nonuniform nested children while preserving exact ownership?
4. **Borrow and region boundaries:** How should aliases, protected branches,
   sections, and replacement compose so that release credits cannot escape their
   lifetime region and old/new overlap remains explicit?
5. **Modular resource interfaces:** How can inferred reservations, scalar state,
   ownership transformations, and resource requirements survive generic and
   cross-crate interfaces without exposing allocation bookkeeping in user code?
6. **Model guarantees and validation:** What independent checks or formal
   correspondence arguments would best validate the analysis against its stated
   source semantics? If physical-memory guarantees are desired later, which
   target/compiler/allocator assumptions must become explicit?

Any extension should preserve the current distinction between exact ownership
metadata and ordinary proved byte ceilings. It should report unsupported
ownership rather than quietly substituting an aggregate estimate.

## 7. Code and evidence map

Paths below are repository-relative links from this document.

| Responsibility | Starting points |
| --- | --- |
| Accounting, kinds, and layout | [accounting.rs](../../../../../source/vir/src/resource/memory/accounting.rs), [footprint.rs](../../../../../source/vir/src/resource/memory/footprint.rs), [layout.rs](../../../../../source/vir/src/resource/memory/layout.rs) |
| Fixed/runtime ownership and metadata | [heap.rs](../../../../../source/vir/src/resource/memory/heap.rs), [elements.rs](../../../../../source/vir/src/resource/memory/elements.rs), [metadata operations](../../../../../source/vir/src/resource/memory/metadata/operations.rs) |
| Checked effects and exported summaries | [checked.rs](../../../../../source/vir/src/resource/memory/transfer/checked.rs), [transfer trace](../../../../../source/vir/src/resource/memory/transfer/trace.rs), [forest algebra](../../../../../source/vstd/std_specs/resource/memory/mod.rs) |
| Shared loop model and recurrence summaries | [loops.rs](../../../../../source/vir/src/resource/memory/loops.rs), [progress.rs](../../../../../source/vir/src/resource/memory/loops/progress.rs), [loop transformations](../../../../../source/vir/src/resource/memory/transfer/trace/loops.rs), [iteration.rs](../../../../../source/vir/src/resource/memory/transfer/iteration.rs) |
| Scalar iterator model and integration | [iterators.rs](../../../../../source/vir/src/resource/memory/iterators.rs), [for_loops.rs](../../../../../source/vir/src/resource/memory/for_loops.rs), [upstream iterator specifications](../../../../../source/vstd/std_specs/iter.rs) |
| Admission and upstream integration | [compiler operation identities](../../../../../source/rust_verify/src/resource/memory/intrinsics.rs), [analysis implementation](../../../../../source/vir/src/resource/memory/mod.rs) |

Readable executable examples:

- [Batched construction](../../../../../examples/resource/memory/heap/loops/batched_construction.rs): repeated helper-produced buffers retained by a collection.
- [Partial transfers](../../../../../examples/resource/memory/heap/loops/partial_transfers.rs): ownership moves while some source storage remains.
- [Peak overlap](../../../../../examples/resource/memory/heap/loops/peak_overlap.rs): temporary versus retained storage during a loop.
- [For construction](../../../../../examples/resource/memory/heap/loops/for_construction.rs): scalar range/adapters constructing owners, including iterator storage.
- [Helper collections](../../../../../examples/resource/memory/vectors/helper_collections.rs): ownership/capacity information crossing helper boundaries.
- [Example index](../../../../../examples/resource/memory/README.md): broader heap, boxed-slice, indexed-owner, and expected-failure examples.

The [memory regression directory](../../../../../source/rust_verify_test/tests/resource/memory)
contains distinct suites for progress, conditional effects, transformations,
indexed/incoming ownership, exits, and for loops. These test accepted behavior,
insufficient bounds, zero/partial traversal, caller-visible ownership after the
loop, and explicit rejection of unsupported programs.

The snapshot commit records passing validation of 901 memory integration tests,
43 resource examples, 25 memory unit tests, and 487 upstream tests, with four
upstream tests ignored. It also records the verifier build, formatting, affected
Clippy checks, strict `vir` rustdoc, compilation/execution checks, and doc-link
validation. These are historical results recorded with that commit; this summary
does not rerun them or establish universal coverage.

Completed task documents are useful scope/history references. Earlier tasks'
original restrictions can be superseded by later tasks; use the current model
and implementation when determining the present boundary, especially
[06](complete/06-iteration-counts-and-state.md),
[07](complete/07-loop-forms-and-exits.md), and
[08](complete/08-for-loops-and-iterators.md).
