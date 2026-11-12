# Memory contracts

A memory contract limits the peak workspace needed by a function or a section of
code. Peak means the most storage needed at once: successive operations can reuse
space, while overlapping storage adds together.

## Writing a budget

Put `resources peak(memory) <= bound` after the function's other specification
clauses. The bound covers the peak over the entire function or section. The
`resources` clause currently supports one memory bound. Functions without this
clause receive ordinary Verus verification only.

| Expression | Meaning |
| --- | --- |
| `ref_size(reference)` | Storage occupied by a reference, excluding its borrowed data. |
| `value_size(value)` | Storage occupied by a non-reference value, excluding separate allocations. |
| `ref_size(&Type)`, `value_size(Type)` | The same measurements using a type instead of a binding. |
| `peak(helper)` | A helper's declared budget, taking the maximum at each conditional. |
| `peak(helper(false))` | Its declared budget for these arguments, without executing the helper. |
| `assert(peak(memory) <= bound)` | A check on the peak reached so far. |
| `assert(current(memory) <= bound)` | A check on memory still live at this point. |

A helper query uses its declared allowance, not a peak inferred from its body.
It does not execute the helper. `peak(memory)` retains its role as the memory
metric in contracts and checkpoints.

Bounds support nonnegative integer literals, immutable unsigned input parameters
(up to 64 bits), these queries, addition,
multiplication, and parentheses. Function bounds can also contain conditionals.
Both size queries accept types or names. Call queries accept scalar constants, immutable
scalar inputs, value-preserving integer widening, comparisons, and Boolean operators.
Formula arithmetic must fit in `u64`. Verus proves this for runtime quantities,
using the function's preconditions. Function bounds can also call numeric spec
functions as described below. Other arbitrary spec expressions and named numeric
constants are not yet supported as budget operands.

## Naming budget formulas

A function budget can call a local `spec fn` returning `nat` or `u64`:

```rust
spec fn element_bytes(capacity: nat) -> nat { value_size(u32) * capacity }

fn collect(capacity: usize)
    requires capacity <= 1024,
    resources peak(memory) <= value_size(capacity) + value_size(Vec<u32>)
        + element_bytes(capacity as nat),
{
    let values = Vec::<u32>::with_capacity(capacity);
}
```

Verus proves the memory inequalities using the specification's definition.
Its body can use ordinary Verus expressions, including `match` and other spec
functions. The formula adds no runtime work. Every selected result and budget
sum or product must fit in `u64`, even though `nat` arithmetic is unbounded.

The initial support requires a nongeneric spec function with a verified body.
Arguments may use immutable scalar inputs, literals, comparisons, casts to
mathematical integers, value-preserving native widening, and nested numeric spec
calls. Executable calls and mutable inputs are rejected. Enum values used only
inside the specification do not add support for executable enums in
memory-checked code.

Use `peak(helper(arguments))` when referring to a helper whose budget calls
a spec function; no constant envelope is inferred from a spec function's body.
Sections and checkpoints still require fixed bounds.

Inside specifications, both size queries return a `nat` using the same model as
memory clauses. They inspect types without evaluating or copying the argument.
Use `ref_size` for references and `value_size` for other values; using the wrong
query is an error. Arrays include their elements and structs include their inline
fields. Boxes and vectors include only their handles: the checker accounts for
their allocations separately. Generic layouts remain unsupported.

A spec function may return a formula that captures its parameters:

```rust
spec fn budget_for(element_bytes: nat) -> spec_fn(nat) -> nat {
    |count: nat| value_size(Vec<u32>) + element_bytes * count
}
```

A function clause can apply it as `budget_for(4)(capacity as nat)`. The factory
must be a local verified spec function; each application uses stable scalar
arguments and the final numeric result must fit in `u64`.
See [named budget formulas](../../examples/resource/memory/contracts/spec_budgets.rs) and
[returned formulas](../../examples/resource/memory/contracts/function_budgets.rs).

## What counts

The model counts live values and owned allocations using a fixed 64-bit policy.
Struct sizes add their fields without padding. `value_size` follows these rules;
it does not report Rust's physical type layout. Native integers use their width
in bytes (`u8`/`i8`: 1, through `u128`/`i128`: 16); `usize` and `isize` both use 8.
Integer arrays multiply that size by their length.

Native integer casts are supported when every source value fits the destination
on both 32-bit and 64-bit architectures, such as `u16 as usize` or `i8 as i64`.
The result uses its destination type's storage. Narrowing, signed-to-unsigned,
and architecture-dependent conversions that could change a value remain
unsupported. Widening also works in allocation quantities and helper queries.

- Parameters count from entry; new locals and results count when produced.
  A move transfers one charge, including across a call or into a result. A copy
  creates another value. Dropping a value ends its charge; last use alone does not.
  An explicitly uninitialized declaration reserves its declared storage.
- Initializing or assigning a value uses its destination's storage. An explicitly
  constructed array, struct, or `Option` without a destination counts once while evaluated.
- Reading, indexing, arithmetic, and borrowing introduce no implicit storage.
  A reference stored in a variable or parameter counts, but its backing data
  remains charged to the owner.
- Ghost locals and proof code contribute no storage. Normal Verus correctness
  checks still apply.

Separate scopes and successive loop iterations reuse workspace. Keeping two
arrays in the same scope requires room for both. See [scope reuse](../../examples/resource/memory/basics/storage.rs)
and [structs](../../examples/resource/memory/algorithms/structs.rs).

## Composing function budgets

During a call, the caller keeps its own live storage and also needs room for the
callee's declared budget. Argument evaluation must fit too. The callee's budget
already includes its parameters and result. When the call initializes an existing
destination, the result shares that charge once produced. Earlier callee work
still overlaps the destination.

Using `peak(helper)` lets a caller follow changes to the helper's contract.
It uses the declared allowance even when the helper currently needs less, so the
helper can change within that allowance. Both functions are checked independently.
For conditional helpers, actual calls use the allowance selected by their
arguments. A caller can write `value_size(flag) + peak(helper(flag))` to forward
that promise, or use a precondition to justify a smaller fixed bound.
See [calls](../../examples/resource/memory/algorithms/calls.rs) and
[argument-specific budgets](../../examples/resource/memory/contracts/call_budgets.rs).

## Returning and using values

Checked helpers can return native integers, `bool`, fixed integer arrays,
concrete structs, and `Option<T>` with supported payloads, including owners. Results
use tail expressions, including value-producing blocks. Non-owning results can
also use `if` and `match`.

A result starts counting when it is produced, so it need not overlap earlier
scratch work. Moving an existing value into the result transfers its charge,
even when different branches return different values. Copies and fresh results
still require separate storage. These are source-level rules, independent of
compiler optimizations.

See [returned buffers](../../examples/resource/memory/basics/returns.rs)
and [retaining too many results](../../examples/resource/memory/expected-failures/returned_buffers.rs).

`Option<T>` costs one tag byte plus `value_size(T)` in either variant, regardless
of Rust's physical representation. `Some`, `None`, by-value
`match`/`if let`, `is_some`, `is_none`, and `unwrap` are supported. Each named
match binding gets its own slot for that arm. Verus still requires proof that
`unwrap` receives `Some`. See [using a popped value](../../examples/resource/memory/basics/options.rs).

Returning references, borrowed temporary results, and match guards remain
unsupported. Early returns follow the exit rules below.

## Fixed-size heap objects

`Box<T>` can own one fixed-size value. `value_size(Box<T>)` counts the owning handle
(8 model bytes); the live heap object adds `value_size(T)` to live memory. A
`Box::new` initializer uses that object's storage, following the same destination
rule as local initialization. Allocator metadata, padding, and physical allocation
strategies are outside the model.

Moving a box transfers its heap charge. Borrowing its contents
keeps that charge with the owner. Explicit `drop` or the owner's scope exit releases
both the handle and the heap object.
See [heap buffer reuse](../../examples/resource/memory/heap/heap.rs) and
[two allocations that exceed their allowance](../../examples/resource/memory/expected-failures/heap_overlap.rs).

Whole-owner reassignment and custom destructors are unsupported. Fixed owning
children can be extracted and replaced as described below. Branches, loops, and
budgeted sections may create and consume their own boxes, but cannot move or drop
owners from outside that region. Custom allocator types remain unsupported.

## Fixed-structure nested ownership

Concrete structs may contain boxes, vectors, boxed slices, and other supported
owning structs. Boxes may contain these values too, including `Box<Vec<T>>` and
nested boxes. Layouts count inline storage: a struct includes its fields' handles,
and a boxed vector's heap object includes the vector handle. Separately owned
allocations are additional charges, each retaining its memory kind and identity.
For example, `Box<Vec<u32>>` with capacity 4 counts an 8-byte outer handle,
a 24-byte heap-resident vector handle, and 16 bytes of vector backing storage.

Whole-value moves transfer the ownership tree. Constructors may combine fresh
allocations and input owners; helper results preserve both kinds of provenance.
Dropping a value or leaving its scope releases its entire owned tree. Borrowing
contents and updating non-owning fields/elements preserve those allocations.
Nested vectors support length, indexing, slices, popping, and pushing. Each child
has independent capacity and retained-byte state. Growing a child counts the old
and replacement buffers together at the peak, alongside its enclosing and sibling
allocations. Helpers may borrow a vector field or its containing struct or box;
inferred reservations and retained allocation effects follow the affected child
paths across calls, including returned owners. See [nested ownership](../../examples/resource/memory/heap/nested_ownership.rs)
and [nested growth](../../examples/resource/memory/vectors/nested_growth.rs).

Fixed owning children support partial moves, explicit drop, reinitialization,
and replacement through struct fields and boxed contents. Detaching a child
transfers its complete allocation tree without copying or releasing it. Replacing
a child evaluates the new value while the old child is still live, then drops
the old tree. Siblings retain their allocations and independent capacity state.
A partially moved parent's inline storage, including any enclosing box storage,
remains charged until the parent's lifetime ends; an extracted local receives its
own inline slot. Scope exit releases only children still attached to the parent.

Input allocation provenance is tracked separately for each fixed node. Helpers
can return selected children or rearrange them without retaining discarded
siblings. Helpers may also replace children through borrowed parents. These
borrowed calls conservatively retain the caller's old allocations throughout the
call, then install the final child ownership and capacity facts. See
[child transfers](../../examples/resource/memory/heap/child_transfers.rs).

Moves and replacements of persistent enclosing owners or their fixed children
across branches, loops, or memory sections remain unsupported, as do extraction
from temporary containers and direct moves out of borrowed owners. Supported
collection operations can extract children from borrowed containers. Recursive layouts and owning array
elements remain excluded. Shared ownership needs
last-owner release rules.

## Runtime collections of owners

A supported type's ownership consists of its own allocations, fixed children,
and runtime child collections. Each runtime collection maintains a sum of child
allocation bytes for each memory kind. Its backing buffer accounts separately
for the elements' inline storage. This composition applies recursively to any
supported concrete element type, including boxes, vectors, boxed slices, and
owning structs; there are no rules for particular nesting combinations.

Vectors of owners support construction, length, insertion, whole-value moves,
helper calls, and drop. Insertion transfers the child's complete allocation
footprint into the collection. Growing the outer buffer overlaps old and new
element storage without duplicating the children's allocations. Dropping the
collection releases both its buffer and all accumulated child storage. Conversion
to a boxed slice transfers the same child sums.

Checked iteration effects generate supported scalar and collection-length
invariants, including multiple appends and branch-selected prefixes. Other
logical relationships still need ordinary loop invariants. Generated, checked
invariants also bound the accumulated child bytes. Helper interfaces involving
runtime owning children require a precise ownership transformation; a byte bound
alone is insufficient.
See [owning collections](../../examples/resource/memory/vectors/owning_collections.rs).

Indexed elements support reads, scalar mutation, growth, and replacement, both
directly and through checked helpers. The same ownership shapes apply through
arbitrary supported combinations of fixed and runtime children. Pass indexed
borrows directly to an operation or helper; allocation effects through a stored
reference alias are not tracked. Bind allocation-changing replacement expressions
to a local first. See [indexed owners](../../examples/resource/memory/vectors/indexed_owners.rs).

Locally modeled children retain individual allocation metadata. An indexed borrow
temporarily separates the selected footprint, uses its reservation facts, and
returns the updated footprint to the collection. Replacement releases the displaced
child's charge. `pop` and `remove` transfer the selected footprint to their result;
dropping the container leaves an extracted child's allocations charged independently.
`remove` also shifts the surviving metadata indices. Owning `Option` values support
construction, unwrap, matching, calls, and drop. See
[element transfers](../../examples/resource/memory/vectors/element_transfers.rs).

Checked helpers describe how allocation forests become their results and modified
arguments. Calls require precise metadata for their owner arguments. Fresh
collection constructors, whole-owner transfers, and supported append operations
preserve individual child reservations without additional contract syntax.
The structural traversal handles fixed children and runtime children separately,
so supported ownership shapes compose without rules for each nesting combination.
Loop summaries compose ordered effects on disjoint persistent collections. An
iteration can append an ordered block, remove several children, or transform
selected children before moving them to a destination. Direct operations,
precisely summarized helpers, and completed nested counted loops use the same
forest operations. Block length counts logical children independently of bytes;
collections can occupy fixed fields of the same owner.

A transformed child retains its individual nested allocation descriptors.
Extraction, fixed-field replacement, buffer growth, conversion to a boxed slice,
and release compose before insertion or drop. Source and destination child types
can differ. Ordered blocks can discard selected children or change their output
order. A generated block describes each iteration separately, including
nonuniform capacities, and its cost is the sum of those actual forests. Affine
footprints also have a symbolic sum, without unrolling the iteration count.
Original-input regions follow the same selection map and exclude fresh storage.
Temporary iteration symbols are closed before a helper summary is exported.
Optional results retain each visit's presence tag, including removals after a
source becomes empty.

Allocation sizes admit native `+`, `-`, and `*` over immutable scalar observations
and supported loop-carried integer locals. A bound scalar can also observe a
selected child's logical length. Executable overflow checks remain in force,
and mutable observations are captured at the allocation. Body proofs use checked scalar
ceilings proposed from symbolic loop-invariant bounds and visit intervals,
including per-operation allocation bounds and entry headroom for temporary
storage and helper work. Nested visits preserve their actual outer-state counts.
These proof ceilings do not replace individual descriptors. Payload values and
scalar dependencies that cannot be represented remain unsupported.

A shared comparison-gap model handles strict and inclusive comparisons in both
directions, literal integer strides, countdowns, and supported collection-length
changes. Both comparison operands may change if their relative gap closes by a
positive constant. Several removals per visit include a partial last block.
Additional integer locals may have constant additive translations; their exit
values remain available after the loop. Zero visits preserve the entry state.
Definitions of immutable scalar locals, such as a capacity derived from the
input count, are preserved as checked loop invariants when they close over
stable values. They do not freeze dependencies on enclosing mutable counters.
Nontranslation and payload-dependent progress remain unsupported. Comparing two
shrinking lengths that saturate at zero also remains unsupported: saturation can
change their relative stride. Arithmetic around shrinking-length progress also
needs a richer checked relation. Native overflow and termination obligations
remain separate from resource progress proofs.

### Loop forms and exits

`break`, `continue`, and `return` carry their live storage and ownership through
the scopes they leave. Locals in those scopes are released; an owning result
stays allocated. Exited paths retain their peak history but do not contribute
live storage or earlier peaks to an unrelated continuing path. Loop exits also
retain the peaks of preceding completed iterations. Memory sections compose
their declared allowance on every exit and retain any escaping result separately.
Direct result moves reconnect their inline lifetime to the enclosing section's
ledger. Evaluating an exit result cannot drop or otherwise spend an enclosing
owner's release credit inside the section; such operations remain unsupported.

Loops with no local back edge use Verus's existing nonisolated proof form, with
its no-back-edge flag. This preserves their actual entry state through nested
and labelled exits, including value-producing breaks. Reusable loops keep their
ordinary inductive proofs. Head-only facts are not exported past a partial visit;
exact completed-count exit predicates are proved on all admitted head breaks.

Precise counted ownership summaries admit effect-free inequality guards at the
loop head. A guard can refine the same counter comparison as a while condition,
or supply the stopping comparison for an unconditional `loop`. Multiple matching
boundaries intersect. Current-loop continuations can skip work under the stable
scalar flags and counter thresholds supported by conditional iteration effects;
the complete visit must still establish its checked scalar progress. Incoming
allocation regions and complete child forests survive these transformations.

Value-producing breaks in reusable loops, partial-visit exits that change fixed
ownership roles or original input regions, and unrepresentable stopping counts
remain unsupported. Runtime ownership interfaces still require precise summaries.
Different exits may return the same owning proof state, including a collection
with branch-dependent children, or matching fresh fixed allocation layouts; different
returned vector states and frozen descriptors cannot share a byte-only result.
Exits inside operands or call arguments are also unsupported.

`for` supports finite half-open native integer ranges, including signed bounds,
and compositions of the standard `rev`, `skip`, and `take` adapters where Rust
and Verus support the combination. The range stores two bounds; `skip` and `take`
each add one `usize` counter. Reversal adds no fields. The Verus wrapper retains
the native iterator; its ghost index, snapshot, and history add no runtime
storage. Iterator setup, argument overlap, next results, and yielded bindings
are charged independently of the collection being built. A scalar `_` pattern
evaluates its initializer without introducing a named slot. See
[for-loop construction](../../examples/resource/memory/heap/loops/for_construction.rs).
Checked iterator factories preserve their scalar state through call summaries;
ordinary logical postconditions still need to establish the count used by a
caller's Verus proof.

Successful visits use the same checked effects, finite counts, and heap proofs
as while loops. The actual wrapper index and exhaustion contract check those
counts. Nested loop queries use Verus's saved pre-advance wrapper snapshot for
facts about the containing visit's head. Continues preserve supported guarded
effects, and single-visit breaks preserve conditional output forests. Partial
early exits still require a representable stopping transformation before a
runtime ownership interface can export a summary; local cleanup alone cannot
provide that summary.

Inclusive ranges, borrowed or owning element iterators, and other adapters remain
unsupported. Iterator state without a precise producing operation cannot supply
a runtime ownership summary. For loops must retain the standard generated Verus
iterator invariants. Unknown iterator classes never inherit the scalar range's
zero-heap rule.

Zero and partial ranges preserve unconsumed children and backing. Unchanged
whole-child transfers use an exact inverse index map, preserving different
capacities and reversing last-element extraction order at the destination. Ordered extraction followed
by restoration of the same whole children can reduce to an unchanged collection,
including through nested counted loops.

Evolving collections use an ordered forest recurrence: each visit reads the
previous visit's result. This covers repeated updates to one child, traversal
of distinct children, indexed replacement, removal with shifted indices, and
pop/change/restore on the same collection. Runtime paths compose through fixed
fields, boxes, and nested collections. Indexed loans can call precisely summarized
leaf helpers, including helpers containing a completed recurrence. Untouched
subtrees retain their descriptors. Replacing a class of children retires uniform
reservation candidates that the new allocations might not satisfy; individual
reservations remain in the descriptors. Read-only loans restore the saved forest.
Stationary-path overwrites and affine descriptor updates can expose complete
closed forests for larger counts, with checked base and successor equations and
a generic induction. Other recurrences retain their exact representation and
need further proof support; finite unfolding is not an ownership approximation.

Indices can use supported pure scalar arithmetic and metadata observations.
Bounds and overflow checks still apply to the executable operations. A trip-count
observation must remain unchanged parametrically, rather than merely have the
same value on the first visit. Small finite cases are exposed automatically;
more general cost and indexed-view induction for evolving recurrences remains
limited. Unsupported scalar dependencies and effects during index evaluation
still reject.

Every intermediate allocation peak remains checked, including old/new backing
overlap. A pop preserves backing and supplies its previous length as a capacity
lower bound, so restoration can reuse those slots.
Counted loops also support conditional appends, last-element removals, and routing
an unchanged whole child to alternative destinations. Conditions may use immutable
scalar parameters or compare affine counter expressions with scalar thresholds
built from those inputs and constants, combined with `!`, `&&`, and `||`.
Thresholds partition the iterations
into ordered ranges with exact widths; each range selects a complete ownership
program. Empty selections preserve the entry forest. Children retain their
individual capacities and order across the selected ranges. Persistent fixed
ownership slots must agree at branch joins; iteration-local children can move
into different destinations when both branches consume them.

Payload-dependent decisions and nonlinear counter predicates remain unsupported.
Every represented branch program must satisfy the block composition rules;
relationships between separate decisions are not solved to rescue incompatible
programs. Symbolic expansion is bounded to six distinct
decisions and sixteen threshold boundaries. These limits reject explicitly rather
than discarding child metadata.

Generated invariants prove local child-charge conservation across transfers,
including the combined sum for alternative destinations. Uniform reservation
lower bounds join across contributing branches; exact child descriptors stay
separate. Callee peak budgets still cover temporary allocations and buffer
replacement.
See [helper collections](../../examples/resource/memory/vectors/helper_collections.rs).

A collection passed into a helper can be indexed to borrow, grow, or replace an
owning child, including through nested fixed and runtime ownership paths. Its
original allocations remain charged to the caller throughout the call. The helper
tracks its own new allocations by child path, and its ownership summary updates
the caller's complete forest. Zero bytes charged inside a helper do not imply an
empty incoming allocation or establish its capacity.

In straight-line code, a helper can also use `remove` or `pop` on a borrowed
incoming collection and return the owning child. `pop` returns `Some(child)` or
`None` according to whether the collection was nonempty. The caller partitions its
complete allocation metadata between that result and the remaining collection; either
can then be dropped independently. The same rule covers nested child shapes and
fixed or indexed paths to the borrowed collection, without new contract syntax.

Straight-line `remove` and `pop` also support collections passed by value. Incoming
allocation lifetimes split between the removed child and the remaining collection,
including nested owners and partial moves from the child. Dropping either owner
inside the helper releases only its own input regions; allocations made inside
the helper remain separate charges. Repeated removals use the reindexed remainder.
An empty `pop` has no child allocation charge and retains the collection's backing
storage; a successful pop transfers the last child's allocations into `Some`.
Indexed replacement, including fixed fields inside an element, releases the
displaced input subtree after evaluating the replacement. Later `remove` and
`pop` preserve the replacement's allocations and the surviving original children
separately. Leaf helpers that replace fixed children follow the same rule, with
the original subtree kept live throughout the leaf call.

Leaf-only results preserve inferred reservation and cardinality descriptors.
Helpers that traverse internal owning collections require a precise summary even
when their public result is a leaf owner; forwarding helpers retain that interface.

Missing ownership support is an error even with a generous memory budget. A helper
whose control flow or value dependencies cannot be represented by a finite ownership
transformation is unsupported. The loop rules above apply to local collections,
owned inputs, and borrowed inputs. Incoming indexed updates, replacement,
extraction, and helper delegation share the same descriptor transformations.
Helpers preserve the caller's remaining allocations and transferred results
independently, including through nested runtime paths. Calls require recoverable
logical geometry and precise ownership metadata; zero local charge never means
that an incoming child is absent, nor does it establish its physical capacity.

Original allocations and this frame's new storage have separate lifetime
regions. Borrowed storage stays charged throughout the call; owned storage follows
its checked partitions at intermediate peaks and final outputs. Wrapping an
incoming owner in a fresh struct or box preserves this distinction. Incoming
extraction and replacement remain unsupported within protected ordinary branches
and memory sections; checked loop branches can partition supported persistent roles.
Other scalar recurrences and control forms retain the limits described above.
There is no aggregate ownership fallback or copied parent charge for an unknown child.
Conservative upper bounds remain valid for byte sizes and peak usage.

Loop entry bounds, forest sums, and uniform child reservation facts are checked
at entry and on back edges. Algorithms that need stronger bounds can still fail
verification. Slice views of owning vectors remain unsupported; owning boxed
slices support direct indexing when their child metadata is available. An enclosing
collection cannot gain child allocations inside a separately budgeted memory section.

## Runtime-sized boxed slices

`Box<[T]>` has a 16-byte owning handle and a backing extent of
`length * value_size(T)` bytes. Elements must have supported fixed inline layouts;
their owned allocations are separate child-footprint sums. `value_size(Box<[T]>)`
measures the handle; it does not include backing storage or child allocations.
Zero-sized elements require no backing bytes.

Convert a named vector with `v.into_boxed_slice()`. The model conservatively
allows a length-sized replacement to overlap the old vector buffer, even when
an allocator could reuse or shrink that buffer in place. After local conversion,
the boxed slice retains its new backing allocation and the original child sums.
For an incoming owning collection, its opaque input provenance is retained with
the children, conservatively keeping the caller's old backing charge too.
The length is captured before the vector is consumed, so later accounting cannot
read a moved value. Moves, helper calls, explicit drop, and scope exit reuse the
ordinary ownership rules. Indexed owning elements use the same child metadata
rules above. See [boxed slices](../../examples/resource/memory/heap/boxed_slices.rs).

A returned local runtime extent that cannot be expressed using immutable scalar
inputs is conservatively bounded by the producing function's checked memory bound.
That bound follows the result through callers until drop; forwarding an input
preserves its existing allocation charge. Local accounting uses the captured
extent. This can make callers require more allowance than the exact payload size.

Other construction/conversion APIs, including boxed-array unsizing and conversion
back into a vector, are not yet modeled. Shared owners remain unsupported.
Bind the vector before converting it, and bind the
result before passing it to a helper.

## Vector allocations and growth

A `Vec<T>` handle costs 24 model bytes. `Vec::new()` begins without backing
storage; `Vec::with_capacity(n)` initially charges `n * value_size(T)` bytes,
even when empty. Capacity information is tracked by the verifier.

A push that fits uses the existing buffer. Otherwise the model allows growth
when the budget covers both the old buffer and its replacement at once. After
replacement only the retained buffer counts. The source model chooses a new
capacity of `max(minimum, 2 * old_capacity, length + 1)`: the minimum is 8 elements
for one-byte elements, 4 for elements up to 1024 model bytes, and 1 for larger
elements. Zero-sized elements require no backing bytes. This is an explicit
abstract allocation policy; allocator rounding, metadata, physical type padding,
and correspondence with other library growth policies are outside the guarantee.

When only a capacity minimum is known, the checker conservatively considers
possible growth using the current length. It tracks the reservation minimum
separately from the retained-byte upper bound. Branches preserve their allocation
states, and loops receive compiler-generated, proof-checked memory invariants;
ordinary loop invariants supply relationships outside the generated progress and
length classes.

`pop` retains backing storage. Moves transfer its charge and dropping releases
it. For non-owning elements, length, indexing, popping, and borrowing elements
through slices remain supported. Owning elements use the collection rules above. Explicit
`reserve`, shrinking, vector replacement, and local reference aliases remain
unsupported. Bind arguments before calls if evaluating them changes vector
allocations. A memory section can grow its own vectors; an enclosing vector
must still fit its existing reservation inside that section.

Constructor capacities can be literals or immutable unsigned variables.
Budgets can scale with inputs, using `value_size` to express storage costs
for the handles and elements rather than unexplained byte totals. See
[growing vectors](../../examples/resource/memory/vectors/vector_growth.rs),
[preallocated vectors](../../examples/resource/memory/vectors/vectors.rs), and
[unbudgeted growth](../../examples/resource/memory/expected-failures/vector_growth.rs).

## Vector helpers and inferred reservations

Helpers can accept `Vec<T>`, `&Vec<T>`, or `&mut Vec<T>`. A reference costs
8 model bytes; the caller retains the backing allocation charge during the call.
The verifier tracks reservations internally, including through nested helpers.
There is no capacity annotation.

```rust
fn append(values: &mut Vec<u32>, capacity: usize, value: u32)
    requires old(values).len() < capacity,
    ensures final(values)@ == old(values)@.push(value),
    resources peak(memory) <= ref_size(values) + value_size(capacity) + value_size(value),
{
    values.push(value);
}
```

This budget covers the helper's parameters and leaves no room for a replacement
buffer. From the length bound, the verifier infers that the incoming vector
needs at least `capacity` reserved elements. It checks every push in the helper
against that reservation and checks every call against the caller's tracked
allocation. These are ordinary proof obligations: inference adds no assumptions
about vector length or contents. A caller with insufficient reservation fails
verification even if its own budget is larger.

Inference recognizes length comparisons with constants and immutable unsigned
inputs in preconditions, branch guards, and loop conditions. It accounts for
successive pushes, propagates requirements through checked helpers, and preserves
conditions depending on scalar inputs. Loop proofs still need ordinary length
invariants. This is conservative inference, not a general solver for arbitrary
length formulas; when a candidate cannot be proved, verification fails.

Reading, indexing, popping, and forwarding a read-only vector need no reservation.
A smaller inferred requirement does not shrink the caller's reservation. Ordinary
`ensures` clauses describe updated lengths and contents for subsequent operations.
When a helper's budget covers growth, it can allocate replacement buffers and its
summary updates the caller's retained-byte bound, conservatively using the
helper's declared allowance when necessary.

A vector helper's memory guarantee is contextual: inferred reservations must be
satisfied by its caller. Keep allocation and helper calls inside checked code to
establish the complete guarantee; an unchecked caller does not establish those
resource requirements merely by satisfying the ordinary `requires` clause.

Borrowed owner bindings must be immutable (their contents may be mutably
borrowed), and vector arguments must resolve to named owners or borrowed parameters,
possibly through fixed field and box-content paths.
Local reference aliases and replacement through `&mut Vec<T>` remain unsupported.
See [vector helpers](../../examples/resource/memory/vectors/vector_helpers.rs).

## Passing heap ownership between helpers

Helpers can consume or return boxes, vectors, or supported owning structs. The
helper's budget covers its handles and additional storage. Checked lifetime summaries tell callers
when an incoming allocation stops counting: dropping it before later scratch
work avoids charging the two together. This also works through nested calls.

The declared allowance still applies, including unused slack. Lifetime summaries
come from the checked body, so changing when a helper drops an input can change
its callers' memory requirements even if its numerical allowance stays the same.

A returned allocation stays charged under its new owner. Forwarding an input
preserves its existing charge; returning a fresh allocation adds that storage to
the caller's live memory. The checker derives these transfers from the helper's
body. See [ownership transfer](../../examples/resource/memory/heap/ownership.rs) and
[an overlapping-allocation failure](../../examples/resource/memory/expected-failures/heap_returns.rs).

Returned vectors preserve their reservations, including capacities supplied through
immutable scalar inputs. Callers can use them to prove subsequent pushes fit.
See [a vector factory](../../examples/resource/memory/vectors/vector_returns.rs).
For now, fresh returned capacities must depend only on literals or immutable inputs.
Owning results can follow a tail expression or a supported explicit exit. Direct
conditional owning expressions remain unsupported; early returns use the exit
rules above.

## Dividing work into sections

A section gives one part of an operation its own workspace allowance:

```rust
fn work()
    resources peak(memory) <= 2 * value_size([u32; 4]),
{
    let original = [1u32, 2, 3, 4];
    resources peak(memory) <= value_size(original) {
        let copy = original;
        assert(peak(memory) <= value_size(copy));
    }
}
```

The section accounts only for its own work. The function remains responsible for
`original` plus the section's declared allowance. Nested sections follow the same
rule; sibling sections can reuse their allowances. A generous outer budget does
not excuse an inner section exceeding its own bound.

See [nested sections](../../examples/resource/memory/contracts/sections.rs).

## Checking progress

`peak(memory)` refers to the peak since entry to the nearest budgeted
section, or the function when outside a section. Ordinary blocks do not reset it.
Storage that has gone out of scope still contributes to that earlier peak.

`current(memory)` measures memory still live at the assertion. Releasing storage
can lower this value without lowering `peak(memory)`. Both queries use the nearest
budgeted section or function; a section excludes its parent's live storage.

A `peak(memory)` checkpoint inside a loop must cover previous iterations within
its accounting scope. A budgeted section inside a loop starts fresh each time it is entered.
Current-memory checkpoints inspect only their execution point, without adding
earlier iterations' peaks. Checkpoints check bounds independently of ordinary
proof assertions.

See [checkpoints](../../examples/resource/memory/contracts/checkpoints.rs) and a
[checkpoint that fails](../../examples/resource/memory/expected-failures/checkpoint.rs).

## Giving different inputs different allowances

A conditional function budget can select its allowance from the inputs:

```rust
resources peak(memory) <= value_size(large)
    + if large { value_size([u32; 8]) } else { value_size([u32; 4]) },
```

Verus proves that the executed branch fits the selected allowance. Preconditions,
preceding proofs, and loop invariants can help establish this, including proving
that an expensive branch is unreachable. The verifier still determines the
storage charges automatically. See the [conditional example](../../examples/resource/memory/contracts/conditional.rs).

Currently, conditions support comparisons and Boolean operators over immutable
`bool` and all native integer inputs. Actual calls can also select allowances using
immutable scalar locals. Mutable selectors and expressions outside this subset
retain the conservative maximum. Argument-free `peak(helper)` always uses
that maximum.

Fixed and conditional budgets both check costs on the paths that execute them.
Preconditions, branch conditions, and loop invariants can prove an expensive path
unreachable. Input-dependent call allowances are proved at the call site.

Sections and checkpoints require fixed bounds; constant call queries work in both.
Runtime allocation charges are also checked against these fixed bounds.
Checkpoints preserve the argument-specific allowance used at each call, including
the proofs that select it; an unselected larger allowance does not inflate the peak.

## Current scope

Checked functions must be safe, nongeneric, and have a verified body.
The supported subset includes `bool`, all native integers, fixed integer arrays,
concrete structs, `Option` values with supported payloads, fixed-size boxes, boxed slices,
vectors with supported growth, and references/slices of supported non-owning values,
indexing, branches, supported while/unconditional/for loops and exits, and calls to
checked functions in the same crate. Integer addition,
subtraction, multiplication, and signed negation retain Verus's overflow checks.
See the [integer example](../../examples/resource/memory/basics/integers.rs).

`char`, floating-point types, other heap-owning types, destructors, enums other
than `Option`, generic structs, recursion, closures, and cross-crate calls are
not supported. Structs with ghost/tracked or reference fields are also
excluded. Destructuring outside supported Option patterns, division, and casts
other than supported value-preserving integer widening remain unsupported.
Loop and exit restrictions are described above. An unsupported construct produces an error rather
than silently receiving a zero cost.

A failure identifies the declaration, call, or checkpoint that cannot fit its
bound. The [array-copy example](../../examples/resource/memory/expected-failures/array_copy.rs)
shows a complete program deliberately rejected for exceeding its allowance.

The analysis merges identical live states at branch joins. It reports an explicit
complexity error above 1,024 distinct ownership alternatives rather than allowing
unbounded path expansion. Checked helpers can divide such a function into smaller parts.

## Memory kinds in the accounting model

The accounting core retains a memory kind alongside each charge. Current source
values and owning handles use `host.local`; box objects and vector backing storage
use `host.heap`. Local storage remains an abstract source-value cost, not a physical
stack measurement. Type layout queries remain byte sizes: placement determines
which kind receives the charge.

Kinds are namespaced identities, rather than a closed enumeration. A future model
can introduce identities such as `device.0.vram` without changing the accounting
arithmetic. Supporting an allocator still requires checked rules for allocation,
release, and ownership transfer; naming a kind does not provide those rules.
Moves and returned allocations preserve their kind. Copying to another memory
kind requires a separate charge while both allocations are live.

Footprints retain simultaneous charges through branch joins, checkpoints, and
function lifetime summaries. A selection can include one kind or a set of kinds;
its peak is computed by selecting usage at each point and then taking the maximum.
For example, successive phases using 100 local bytes and 100 heap bytes have a
combined peak of 100, even though each individual kind peaks at 100.

`resources peak(memory)` clauses bound total usage. Internally, budgets
pair a memory selection with a byte expression, and proof obligations project the
footprint onto that selection. Reports expose the same selection mechanism.
Source syntax for kind-specific clauses and device allocator models are not yet
provided. A helper or section with only a total contract may spend its unused
allowance in any kind; category queries conservatively retain that freedom rather
than inferring a category-specific promise from the current implementation.
