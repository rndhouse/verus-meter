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
Register their modes for resolution inference, use fresh AST identities, and
commit state updates after the executable operation. Generated loop invariants
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
Infer them from checked executable bodies and compose them bottom-up through
helpers. Instantiate against snapshots of eligible local owners; ordinary callee
peak profiles still keep incoming storage charged throughout the call. Fixed
descriptor properties and runtime forests are separate template inputs. Logical
counts describe occupied elements independently of byte bounds and reservation
minima; snapshot a count before its source becomes inaccessible, such as when
moving beneath an optional payload. Runtime ownership interfaces require a
template, and calls require precise argument metadata. Missing inference or
metadata is unsupported, never an aggregate fallback. Interface consistency
checks reject disagreement about results and affected borrowed parameters;
these checks do not prove equivalence of complete forest expressions.
Commit borrowed effects into existing proof-state IDs so
branch joins and loop invariants observe the updated allocations.
By-value optional patterns join parametric branch states. Collection loop
summaries interpret a representative iteration and require one unconditional
persistent append or pop. A fresh iteration symbol rejects index-dependent
footprints; stable bounds and isolated effects justify repetition or prefix
retention over complete child forests. Reservation lower bounds remain separate
from the conservative append-only backing-byte upper bound.

[Indexed projections](../../source/vir/src/resource/memory/projections.rs) loan a
selected footprint from a precise collection and return its final descriptors.
Finish nested loans from the inside out, after child updates commit. Pending
cost proofs precede peak checks; validity proofs follow the operation. Indices
must remain stable across argument evaluation. Pure projections and `spec_vec_index`
avoid repeating executable indexing or its bounds checks.

[Extraction](../../source/vir/src/resource/memory/extraction.rs) transfers storage
into an independently owned result, including conditional Option payloads.
Incoming runtime children have abstract provenance; indexing or extracting them
is unsupported until local analysis can represent their individual forests.
Do not duplicate an enclosing charge to stand in for an unknown child.

Loop proofs preserve forest validity and sums, immutable entry facts, and inferred
reservation candidates indexed by fixed and repeated ownership steps. Every
candidate is checked at loop entry and on back edges. Loop-carried helper effects
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
