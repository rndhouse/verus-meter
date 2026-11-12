# Maintaining the fork

Memory checking depends on the shape and ordering of Verus's intermediate code.
A clean Git merge still needs verification of these boundaries.

| Boundary | Fork code and upstream hooks |
| --- | --- |
| Syntax | [syn](../../dependencies/syn/src/verus.rs) defines memory clauses, formulas, sections, and checkpoints; [prettyplease](../../dependencies/prettyplease/src/expr.rs) prints them. |
| Macros | [resource/memory](../../source/builtin_macros/src/resource/memory) extends the [syntax visitor](../../source/builtin_macros/src/syntax.rs). Its child-module declaration follows the quoting macros to preserve their scope and hygiene. |
| Rust translation | [Frontend memory support](../../source/rust_verify/src/resource/memory) translates budget markers and recognizes standard operations by compiler identity. Call lowering, headers, and function translation retain small hooks. |
| Verification pipeline | [query.rs](../../source/rust_verify/src/query.rs) collects execution modes and invokes [pipeline.rs](../../source/rust_verify/src/resource/memory/pipeline.rs). |
| Analysis | [VIR memory support](../../source/vir/src/resource/memory) checks accounting and produces ordinary proof obligations. Shared VIR types and visitors carry its metadata. |

Type-only `value_size` and `ref_size` queries in specifications are resolved before each
function's well-formedness and mode checks, using the shared model layouts.
Both select the existing inline size calculation after checking whether the
argument is a reference; neither follows pointers or includes separate allocations.

[Integer cast classification](../../source/vir/src/resource/memory/model.rs)
admits only range-preserving native conversions on both supported pointer widths.
Body accounting evaluates the operand and charges the destination normally;
capacity expressions and templates retain its exact value. Keep clipping or
wrapping conversions out of identity normalization.

Consumed reads retain Rust's actual result type even when their places contain
implicit dereferences. Child ownership paths require both the source place type
and the selected value type; using the outer box type would transfer the wrong tree.

Keep the memory pass **after all local bodies are mode-checked and before export,
resolution inference, or simplification**. Later transformations can obscure the
source places and lifetimes the model measures. Generated assertions need fresh
AST identities. Erase memory metadata only after analysis succeeds; keep the
assertions for normal Verus verification.

Macro lowering must preserve execution and ghost erasure. Resolve section budget
names before visiting its declarations, and retain binding scopes for checkpoints.
Vector growth introduces compiler-owned spec locals after mode checking.
Register their modes for resolution inference, including nested specification
closure bindings used by generated iteration blocks, use fresh AST identities,
and commit state updates after the executable operation. Generated loop invariants
must be proved at entry and on back edges. Keep peak checks separate from retained
allocation effects; caller-owned buffers must stay charged during helper calls.
Infer reservation requirements bottom-up over the checked call graph. They are
resource requirements, not logical assumptions: prove uses within the helper and
prove each caller supplies the inferred reservation. Keep inference conservative
and preserve proof/spec execution boundaries.

Allocation summaries in [allocations.rs](../../source/vir/src/resource/memory/allocations.rs)
carry memory kinds, byte-size expressions, input provenance, and retained effects.
Lifetime profiles carry temporary peaks, including old/new allocation overlap.
Constructors supply byte extents, so owning call composition does not reconstruct
sizes from return types. Keep container facts, such as vector capacity in elements,
in adapters such as [vector_calls.rs](../../source/vir/src/resource/memory/vector_calls.rs).
New owning containers should reuse these effects and supply only their layout,
operation rules, and any additional proof facts. The [boxed-slice adapter](../../source/vir/src/resource/memory/boxed_slices.rs)
uses shared byte snapshots and replacement overlap for runtime-length allocations.

Keep three concepts distinct: inline value layout, separately owned allocations,
and operation effects. [Ownership trees](../../source/vir/src/resource/memory/heap.rs)
compose fixed children by field or box contents. A node carries only its own
allocation charge; child handles are already included in the enclosing inline
layout. Call summaries can wrap whole input subtrees under fresh nodes, and
lifetime composition must account for every input provenance beneath a root.
Sibling returned allocations need distinct identities even at one call span.
Vector result facts are indexed by the same structural paths as allocation facts.
The shared place resolver in [paths.rs](../../source/vir/src/resource/memory/paths.rs)
accounts for implicit box dereferences and explicit field projections. Use it for
both inferred reservations and call effects so sibling allocations stay distinct.
Input trees carry disjoint provenance IDs at every fixed node. A summary maps
these IDs to parameter paths; call composition splits actual input trees into
nodes and consumes each node once when reconstructing results or capturing
collection children. Lifetime profiles must count each node independently.
Returned input nodes retain original allocation identities and apply only their
own growth effects; their children are composed separately.

[Child transfers](../../source/vir/src/resource/memory/children.rs) detach and
replace owners through the same paths. Replacement evaluates its RHS before
releasing the displaced tree. Partial moves retain the parent's inline charge.
Borrowed replacements export final ownership trees and capacity facts at disjoint
paths; replacing an ancestor supersedes descendant effects. Do not also export
ordinary growth or collection additions beneath a replaced path. Caller-owned
old storage stays charged throughout borrowed calls, conservatively, and is
released when applying the final replacement.
Loop invariants and section protections must visit every descendant vector state.

[elements.rs](../../source/vir/src/resource/memory/elements.rs) represents runtime
children with byte sums by memory kind, independent of container layout. Element
insertion captures the complete child footprint, retires its old charge identities,
and preserves input provenance. Owning call summaries and borrowed effects carry
both newly retained bytes and captured inputs; each captured input is consumed
exactly once at the caller. Additive child effects must never use the maximum
operation used for replacement buffers. Loop sums and append-only buffer bounds
are ordinary proof-checked invariants, not assumptions. Post-operation checks
must include all pending child sums before their erased states commit.

[Allocation metadata](../../source/vir/src/resource/memory/metadata.rs) records
charged byte upper bounds and reservation lower bounds independently. Negative
path components name fixed children; nonnegative components name runtime indices.
Verified [forest algebra](../../source/vstd/std_specs/memory.rs) justifies selection,
partition, composition, and removal with reindexing. Structural serialization and
restoration recurse over supported types, independently of nesting combinations.
Shared [ownership operations](../../source/vir/src/resource/memory/metadata/operations.rs)
define child extraction, reindexing, and replacement for both local accounting and
helper templates. Local accounting schedules snapshots, lifetime changes, and
overlap checks around these descriptor transformations.
Recursive forest selectors, costs and descriptor lookup stay opaque at use
sites. Emit the algebra's proved facts explicitly to keep nested queries from
expanding into large families of sequence indices.

[Ownership templates](../../source/vir/src/resource/memory/transfer/mod.rs) describe
finite physical-forest transformations separately from frame-local charges.
Derive them from the [checked transitions](../../source/vir/src/resource/memory/transfer/checked.rs)
recorded by body accounting, and compose them bottom-up through helpers. These
records supply operation kinds, allocation sizes, child slots, resolved places,
checked growth permissions, and owning scope releases. The symbolic evaluator
specializes scalar expressions and control flow; it must consume every recorded transition before exporting a
template. It must not rediscover ownership operations from source call names or
reconstruct a consumed place from its outer type. Instantiate against snapshots
of eligible tracked owners; ordinary callee peak profiles still keep incoming
storage charged throughout the call. Fixed descriptor properties and runtime forests are separate template inputs. Logical
counts describe occupied elements independently of byte bounds and reservation
minima; snapshot a count before its source becomes inaccessible, such as when
moving beneath an optional payload. Runtime ownership interfaces require a
template, and calls require precise argument metadata. Missing inference or
metadata is unsupported, never an aggregate fallback. Interface consistency
checks reject disagreement about results and affected borrowed parameters;
these checks do not prove equivalence of complete forest expressions.
Commit borrowed effects into existing proof-state IDs so
branch joins and loop invariants observe the updated allocations.
By-value optional patterns join parametric branch states.
[Shared loop records](../../source/vir/src/resource/memory/loops.rs) classify control
forms, scalar writes, direct appends, and helper proof requirements once. Body
accounting adds entry-charge snapshots and input-region boundaries, then publishes
the record with its checked operations. Both the
[inductive proof driver](../../source/vir/src/resource/memory/loops/analysis.rs) and
ownership summarizer consume that record; the summarizer cannot infer an unchecked
loop from source syntax. Source observations select proof candidates, while checked
operations remain authoritative for ownership effects.

[Shared progress](../../source/vir/src/resource/memory/loops/progress.rs) proposes
constant integer translations and comparison gaps independently of ownership
repetition. The [checked evaluator](../../source/vir/src/resource/memory/transfer/trace/loops/progress.rs)
validates the entire visit before publishing counts, scalar exits, or logical
length candidates. The body proof counts actual back edges in erased state and
proves those candidates at entry and on back edges. Conditional ownership uses
the same selected interval programs to describe completed prefix lengths.
Native overflow and loop termination remain ordinary executable obligations.

The checked evaluator also supplies closed definitions of immutable scalar
locals from pure source initializers. Do not infer logical postconditions from a
callee's implementation. Prove and preserve these equalities in isolated queries;
never reuse a first-visit definition depending on enclosing mutable state.

Lexical exit edges in [control.rs](../../source/vir/src/resource/memory/control.rs)
carry live storage and detached results separately from continuing branches.
Unwind each scope once, restore section accounting on escaping edges, and retain
the inline lifetime identity of results moved from the enclosing region. Keep
enclosing owner protection during effectful exit-result evaluation. Retain
earlier completed visits' peaks on loop exits. Rebase accepted head exits onto
the completed head's input-region identities. Single-visit loop records use
Verus's existing nonisolated/no-back-edge proof form; do not invent induction
facts for them. Partial visits cannot export head-only facts. Completed-count
exit predicates are ordinary loop ensures, proved at all accepted exits.
Forest tracing consumes checked exit destinations, keeps suffix effects under
their surviving path guards, and rejects unrepresentable exit dependencies.

[For-loop adaptation](../../source/vir/src/resource/memory/for_loops.rs) retains
Verus's executable wrapper, next call, exhaustion branch, and ordinary proofs.
Normalize its irrefutable wrapper binding and unit body binding only across the
same execution boundaries as accounting. The shared loop record supplies a
successful-visit view to ownership repetition; it must consume the checked next
operation and exhaustion edge. Prove count candidates against the real wrapper
index and sequence length. Within a containing for body, inherited head facts
refer to its pre-advance ghost snapshot, not the already advanced wrapper.

[Iterator rules](../../source/vir/src/resource/memory/iterators.rs) separate
native inline layouts from finite scalar sequences. Compiler datatype and call
identities select the rules. Adapter composition preserves exact selection and
order, including empty sequences. Preserve source order for range field
initializers, and keep earlier arguments charged while later ones execute.
Do not extend these rules to borrowed or owning iterators without
their explicit yield, retained-storage, and cleanup model. Bound generated child
costs over the complete ordinal interval; substituting its final endpoint is
insufficient for decreasing sizes.

Entry snapshots are immutable within a loop invocation. Reuse equivalent length
observations and preserve existing snapshots when freezing headroom facts;
recapturing them would separate progress from charge conservation in isolated
queries. Nested loops must not reuse a persistent role's first outer-visit length
as their own entry constant. Unchanged scalar condition operands retain their
relationship to their entry snapshots.

Loop repetition chooses a representation of the same checked transition.
[Ordered effects](../../source/vir/src/resource/memory/transfer/effects.rs)
normalize disjoint monotone roles into ranges, tiles, or generated blocks.
[Ordered recurrences](../../source/vir/src/resource/memory/transfer/trace/loops/indexed.rs)
apply the shared evaluator to an evolving forest when roles overlap or use runtime
paths. Physical roots and original-input regions occupy separate packed slots,
so repeated visits and removal reindexing see the previous result without mixing
new allocations into original lifetimes. Bind all iteration symbols, retain
count-observation read roles, and publish modified borrowed parameters. Rejected
representations restore the complete evaluator state before another is tried.

[Guarded programs](../../source/vir/src/resource/memory/transfer/trace/loops/guards.rs)
partition counted iterations at stable scalar thresholds. Each ordered interval
selects a complete checked block program; state and original-input regions join
with the same scalar decision. Stable flags select an entire range, while
counter comparisons select exact subranges. Changing payload predicates reject.
Project fixed roles through joins before composing later updates, so unrelated
sibling forests do not become part of each role's expression. Post-operation
reservation candidates join across all contributing branch classes before their
ordinary checks are emitted. Alternative transfer destinations share a connected
charge-conservation group, proved at entry and on every back edge.

Fresh blocks repeat using an indexed forest tiling; removals retain a prefix;
transfers reverse a contiguous source range. These operations have verified cost,
validity, and indexed-view laws. View laws activate only for requested paths;
prefix-cut descriptor laws are instantiated at the relevant range expressions.
This keeps exact forests available without expanding every child in failing-budget
queries. Temporary identities cannot escape a template, and reservation lower
bounds remain separate from backing-byte upper bounds. Evolving recurrences
preserve validity by induction and expose small exact cases for proof automation;
larger counts retain the same recurrence. Stationary overwrites and affine
record updates may propose a complete closed forest. Check its base and successor
equalities, then use the verified closed-forest induction; keep structural
unfolding local to that equation proof. Byte induction includes collection
backing as well as child sums, with checked per-visit allocation ceilings.
Symbolic ceilings use invariant observations and interval arithmetic; completed
nested counts contribute to the containing visit. Pointwise multiplication facts
relate symbolic per-visit bounds to reserved headroom without activating global
nonlinear rewriting. Empty retained ranges expose an empty forest directly,
without unfolding each discarded child.

Composition retains every intermediate peak check. Local proofs use ordinary
inductive charge and backing candidates derived from the completed effects. Nested
queries freeze their parent's completed invariants at their actual entry and keep
ancestor snapshots immutable. Element policies use saved source lengths and the
completed containing iteration, including operations after an inner loop. A body
visit retires first-visit finite extents and known-zero shortcuts: later iterations
must prove their own charge facts. Capacity observations from pop are monotonic
lower bounds, so restored backing does not require equality of modeled capacity
across iterations.

Loop boundaries give changed original-input regions fresh exit identities. Earlier
peak profiles retain first-iteration regions: original allocations can only move
or be released, so their total at corresponding later iteration points cannot
increase. Local allocations remain governed by inductive body proofs. Entry
snapshots and the checked transfer graph supply conservation candidates for sums
across source and destination. Ownership inference returns structural transfer
relationships only with a complete template; the proof driver turns them into
invariants, proved at entry and on back edges. Summary inference never mutates the
body's proof state. Exact exit forests keep subsequent caller accounting and
extraction precise.

[Indexed projections](../../source/vir/src/resource/memory/projections.rs) loan a
selected footprint from a precise collection and return its final descriptors.
Finish nested loans from the inside out, after child updates commit. Pending
cost proofs precede peak checks; validity proofs follow the operation. Indices
must remain stable across argument evaluation. Read-only loans restore their
saved forest and count policy without reconstructing unchanged descriptors.
Indexed replacement clears affected uniform reservation candidates before body
analysis, while preserving other classes and all individual descriptors.
Pure projections and `spec_vec_index`
avoid repeating executable indexing or its bounds checks.

[Extraction](../../source/vir/src/resource/memory/extraction.rs) transfers storage
into an independently owned result, including conditional Option payloads.
Incoming collections use a local-charge view: the caller retains the original
allocations, while an initially empty forest records allocations introduced by
the helper. Indexed loans partition this forest using the same path rules as a
complete forest. Bind selected geometry to the executable child; an absent local
record means zero local charge, not an absent child. Disable exact-capacity
inference from partial byte charges, and do not infer uniform reservations from
changes to one incoming child. The checked transition log identifies mutations;
read-only loans must not export write effects.

The caller applies the helper template to its complete forest after accounting
for the call's peak. `remove` and `pop` from a borrowed incoming
collection use the same partition for local charges and complete caller ownership. Restore
the selected child with the input forest's view; only a complete descriptor or
an executable source can establish cardinality. Record removal before finishing
enclosing indexed loans so they export the mutation. Borrowed input storage stays
charged throughout the call, and result/parent charges separate when its template
is applied. Pop derives its optional tag from the executable length, independently
of local charges; an empty pop selects no runtime child.

[Input provenance](../../source/vir/src/resource/memory/provenance.rs) partitions
incoming lifetimes for extraction, replacement, and loop-carried transfers. Body accounting
replaces one live identity with disjoint remaining and selected identities. The checked
transition evaluator partitions original input descriptors using the same removal
algebra, including reindexing and ancestor paths. Each fixed child gets its own
region; local allocations never enter these original-input expressions. An empty
pop selects empty regions while retaining the parent's backing allocation; the
optional tag and last index follow the same removal operation as the physical
forest. Caller peak profiles instantiate region costs before applying the final ownership
template. Preserve known-zero local charges through descriptor-only updates so
symbolic zero counters do not hide independent input lifetimes. Indexed replacement detaches the displaced subtree from its original input
region after RHS evaluation, preserving old/new overlap in earlier profiles.
Fixed-child replacement effects from leaf calls use the same detachment after
accounting for the call peak. The replacement retains its own charges, so later
extraction cannot recover displaced input allocations. Incoming extraction and
indexed replacement in protected control-flow regions remain unsupported.

[Call provenance](../../source/vir/src/resource/memory/transfer/origins.rs) maps
disjoint original regions at argument and output paths independently of local
charges. Intermediate callee regions get caller identities for peak witnesses;
final regions attach once to returned and borrowed owners. Indexed loans replace
the selected original subtree inside its persistent ancestor. Structural joins
remain visible as ownership mutations even when they add zero local bytes.
Derived lifetimes require a template even with a fixed or unit public result.

[Call geometry](../../source/vir/src/resource/memory/metadata/geometry.rs) supplies
missing incoming descriptors from the executable logical source using zero-byte
records. Existing charged records retain precedence. The complete/local view is
checked throughout fixed ownership trees; templates disable exact-capacity
inference from partial byte charges. Known-zero output charges are normalized
structurally and proved before use. Partition proofs establish nonnegativity on
both sides, including discarded subtrees. Ordered-loop outputs publish requested
inverse removal views at use sites, keeping these laws dormant for ordinary calls.
Missing geometry or ownership metadata remains unsupported. Never copy a parent
charge to stand in for an unknown child.

Loop proofs preserve forest validity, sums, immutable entry facts, and inferred
reservation candidates indexed by fixed and repeated ownership steps. Functions
that export ownership or call templates also preserve runtime-child
classification across their producing loops, including directly built
collections used by later helpers. Keep those classification proofs local.
Every candidate is checked at loop entry and on back edges. Preserve zero local charge
only with an explicit zero invariant for an unchanged or shrinking collection;
possible backing growth invalidates first-visit zero shortcuts. Loop-carried helper effects
that would invalidate precision are unsupported. Shared ownership still needs
separate last-owner release rules.

Activate finite transfer laws at operation sites and broader sibling-view rules
in loop scopes. Isolated loop queries must receive their own algebra activation;
unneeded structural rewrites can make failing budget queries expensive.

Compiler upgrades need a review of borrow/coercion lowering, move/copy provenance,
and the identities used for supported standard operations.

When resolving syntax conflicts, edit the AST definitions first, then run
`cargo run` in `dependencies/syn/codegen/` to regenerate the schema and derived files.
The unreleased contract format has no compatibility variants. Update the model
identity in [model.rs](../../source/vir/src/resource/memory/model.rs) when its
semantics change and rebuild dependent verification artifacts.

After an upgrade, rebuild with `cargo make build` from `source/`, then run:

```sh
cargo test --release -p rust_verify_test --test resource memory:: -- --test-threads=2
cargo test --release -p rust_verify_test --test examples resource_ -- --test-threads=2
cargo test --release -p vir --lib resource::memory
```

Also run `test_resources` from `dependencies/syn/`, the prettyprinter tests, and
upstream regressions covering references, arrays, modes, erasure, and function
contracts. Passing memory tests alone does not establish upstream compatibility.
