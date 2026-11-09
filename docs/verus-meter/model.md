# Memory contracts

A memory contract limits the peak workspace needed by a function or a section of
code. Peak means the most storage needed at once: successive operations can reuse
space, while overlapping storage adds together.

## Writing a budget

Put `mem_peak <= bound` after the function's other specification clauses.
Functions without this clause receive ordinary Verus verification only.

| Expression | Meaning |
| --- | --- |
| `mem_size(Type)` | The type's size in the memory model. |
| `mem_size(value)` | The size of a named parameter or local's type, without copying or evaluating its value. |
| `mem_peak(helper)` | A helper's declared budget, taking the maximum at each conditional. |
| `mem_peak(helper(false))` | Its declared budget for these arguments, without executing the helper. |
| `assert(current(mem_peak) <= bound)` | A check on the peak reached so far. |

Bounds support nonnegative integer literals, immutable unsigned input parameters
(up to 64 bits), these queries, addition,
multiplication, and parentheses. Function bounds can also contain conditionals.
`mem_size` accepts types or names. Call queries accept scalar constants, immutable
scalar inputs, comparisons, and Boolean operators.
Formula arithmetic must fit in `u64`. Verus proves this for runtime quantities,
using the function's preconditions. Function bounds can also call numeric spec
functions as described below. Other arbitrary spec expressions and named numeric
constants are not yet supported as budget operands.

## Naming budget formulas

A function budget can call a local `spec fn` returning `nat` or `u64`:

```rust
spec fn element_bytes(capacity: nat) -> nat { mem_size(u32) * capacity }

fn collect(capacity: usize)
    requires capacity <= 1024,
    mem_peak <= mem_size(capacity) + mem_size(Vec<u32>)
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
mathematical integers, and nested numeric spec calls. Executable calls and mutable
inputs are rejected. Enum values used only inside the specification do not add
support for executable enums in memory-checked code.

Use `mem_peak(helper(arguments))` when referring to a helper whose budget calls
a spec function; no constant envelope is inferred from a spec function's body.
Sections and checkpoints still require fixed bounds.

Inside specifications, `mem_size(Type)` and `mem_size(parameter)` return a `nat`
using the same model as memory clauses. They inspect types without evaluating
or copying the argument. Supported concrete structs use their field sizes.
Generic layouts remain unsupported.

A spec function may return a formula that captures its parameters:

```rust
spec fn budget_for(element_bytes: nat) -> spec_fn(nat) -> nat {
    |count: nat| mem_size(Vec<u32>) + element_bytes * count
}
```

A function clause can apply it as `budget_for(4)(capacity as nat)`. The factory
must be a local verified spec function; each application uses stable scalar
arguments and the final numeric result must fit in `u64`.
See [named budget formulas](../../examples/resource/memory/spec_budgets.rs) and
[returned formulas](../../examples/resource/memory/function_budgets.rs).

## What counts

The model counts live values and owned allocations using a fixed 64-bit policy.
Struct sizes add their fields without padding. `mem_size` follows these rules;
it does not report Rust's physical type layout. Native integers use their width
in bytes (`u8`/`i8`: 1, through `u128`/`i128`: 16); `usize` and `isize` both use 8.
Integer arrays multiply that size by their length.

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
arrays in the same scope requires room for both. See [scope reuse](../../examples/resource/memory/storage.rs)
and [structs](../../examples/resource/memory/structs.rs).

## Composing function budgets

During a call, the caller keeps its own live storage and also needs room for the
callee's declared budget. Argument evaluation must fit too. The callee's budget
already includes its parameters and result. When the call initializes an existing
destination, the result shares that charge once produced. Earlier callee work
still overlaps the destination.

Using `mem_peak(helper)` lets a caller follow changes to the helper's contract.
It uses the declared allowance even when the helper currently needs less, so the
helper can change within that allowance. Both functions are checked independently.
For conditional helpers, actual calls use the allowance selected by their
arguments. A caller can write `mem_size(flag) + mem_peak(helper(flag))` to forward
that promise, or use a precondition to justify a smaller fixed bound.
See [calls](../../examples/resource/memory/calls.rs) and
[argument-specific budgets](../../examples/resource/memory/call_budgets.rs).

## Returning and using values

Checked helpers can return native integers, `bool`, fixed integer arrays,
concrete structs, and `Option<T>` with supported non-owning payloads. Results
use tail expressions, including value-producing blocks, `if`, and `match`.

A result starts counting when it is produced, so it need not overlap earlier
scratch work. Moving an existing value into the result transfers its charge,
even when different branches return different values. Copies and fresh results
still require separate storage. These are source-level rules, independent of
compiler optimizations.

See [returned buffers](../../examples/resource/memory/returns.rs)
and [retaining too many results](../../examples/resource/memory/expected-failures/returned_buffers.rs).

`Option<T>` costs one tag byte plus `mem_size(T)` in either variant, regardless
of Rust's physical representation. `Some`, `None`, by-value
`match`/`if let`, `is_some`, `is_none`, and `unwrap` are supported. Each named
match binding gets its own slot for that arm. Verus still requires proof that
`unwrap` receives `Some`. See [using a popped value](../../examples/resource/memory/options.rs).

Returning references, borrowed temporary results, match guards,
and explicit early `return` remain unsupported.

## Fixed-size heap objects

`Box<T>` can own one fixed-size value. `mem_size(Box<T>)` counts the owning handle
(8 model bytes); the live heap object adds `mem_size(T)` to `mem_peak`. A
`Box::new` initializer uses that object's storage, following the same destination
rule as local initialization. Allocator metadata, padding, and physical allocation
strategies are outside the model.

Moving a box transfers its heap charge. Borrowing its contents
keeps that charge with the owner. Explicit `drop` or the owner's scope exit releases
both the handle and the heap object.
See [heap buffer reuse](../../examples/resource/memory/heap.rs) and
[two allocations that exceed their allowance](../../examples/resource/memory/expected-failures/heap_overlap.rs).

Owner reassignment, extracting owning subvalues, and custom destructors are
unsupported. Branches, loops, and budgeted sections may create and consume their
own boxes, but cannot move or drop owners from outside that region. Custom
allocator types remain unsupported.

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
paths across calls, including returned owners. See [nested ownership](../../examples/resource/memory/nested_ownership.rs)
and [nested growth](../../examples/resource/memory/nested_growth.rs).

Moving or replacing an owning field and moving an owner out of a box remain
unsupported. These need ownership transfer transitions for a particular child
path. Recursive layouts, owning `Option` payloads, and owning array elements are
also excluded. Shared ownership needs last-owner release rules.

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

Ordinary loop invariants provide the logical length bound. Generated, checked
invariants relate direct insertions to that length and bound the accumulated
child bytes. Helper summaries preserve captured input ownership and add newly
retained bytes to the caller's collection. Where a sum cannot be exported using
immutable scalar inputs, the checked function budget supplies a conservative
bound. Byte-only helper effects can make loop proofs less precise than direct
insertion. See [owning collections](../../examples/resource/memory/owning_collections.rs).

Individual owning elements remain opaque to allocation accounting: vector
indexing, slice views, popping, extraction, and replacement need per-element
ownership transitions and are not supported yet. An enclosing collection cannot
gain child allocations inside a separately budgeted memory section.

## Runtime-sized boxed slices

`Box<[T]>` has a 16-byte owning handle and a backing extent of
`length * mem_size(T)` bytes. Elements must have supported fixed inline layouts;
their owned allocations are separate child-footprint sums. `mem_size(Box<[T]>)`
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
ordinary ownership rules. Borrowing and indexing individual elements require
non-owning element types. See [boxed slices](../../examples/resource/memory/boxed_slices.rs).

A returned local runtime extent that cannot be expressed using immutable scalar
inputs is conservatively bounded by the producing function's checked `mem_peak`.
That bound follows the result through callers until drop; forwarding an input
preserves its existing allocation charge. Local accounting uses the captured
extent. This can make callers require more allowance than the exact payload size.

Other construction/conversion APIs, including boxed-array unsizing and conversion
back into a vector, are not yet modeled. Shared owners remain unsupported.
Bind the vector before converting it, and bind the
result before passing it to a helper.

## Vector allocations and growth

A `Vec<T>` handle costs 24 model bytes. `Vec::new()` begins without backing
storage; `Vec::with_capacity(n)` initially charges `n * mem_size(T)` bytes,
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
ordinary loop invariants still need to bound lengths relevant to growth.

`pop` retains backing storage. Moves transfer its charge and dropping releases
it. For non-owning elements, length, indexing, popping, and borrowing elements
through slices remain supported. Owning elements use the collection rules above. Explicit
`reserve`, shrinking, vector replacement, and local reference aliases remain
unsupported. Bind arguments before calls if evaluating them changes vector
allocations. A memory section can grow its own vectors; an enclosing vector
must still fit its existing reservation inside that section.

Constructor capacities can be literals or immutable unsigned variables.
Budgets can use inputs directly, for example `32 + 32 + 16 * n` for a loop
building a `Vec<u32>` with at most `n` pushes. See
[growing vectors](../../examples/resource/memory/vector_growth.rs),
[preallocated vectors](../../examples/resource/memory/vectors.rs), and
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
    mem_peak <= mem_size(values) + mem_size(capacity) + mem_size(value),
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
See [vector helpers](../../examples/resource/memory/vector_helpers.rs).

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
body. See [ownership transfer](../../examples/resource/memory/ownership.rs) and
[an overlapping-allocation failure](../../examples/resource/memory/expected-failures/heap_returns.rs).

Returned vectors preserve their reservations, including capacities supplied through
immutable scalar inputs. Callers can use them to prove subsequent pushes fit.
See [a vector factory](../../examples/resource/memory/vector_returns.rs).
For now, fresh returned capacities must depend only on literals or immutable inputs,
and owning results must follow a single tail-expression path. Conditional ownership
returns and owners inside `Option` remain unsupported.

## Dividing work into sections

A section gives one part of an operation its own workspace allowance:

```rust
fn work()
    mem_peak <= 2 * mem_size([u32; 4]),
{
    let original = [1u32, 2, 3, 4];
    mem_peak <= mem_size(original) {
        let copy = original;
        assert(current(mem_peak) <= mem_size(copy));
    }
}
```

The section accounts only for its own work. The function remains responsible for
`original` plus the section's declared allowance. Nested sections follow the same
rule; sibling sections can reuse their allowances. A generous outer budget does
not excuse an inner section exceeding its own bound.

See [nested sections](../../examples/resource/memory/sections.rs).

## Checking progress

`current(mem_peak)` refers to the peak since entry to the nearest budgeted
section, or the function when outside a section. Ordinary blocks do not reset it.
Storage that has gone out of scope still contributes to that earlier peak.

A checkpoint inside a loop must cover previous iterations within its accounting
scope. A budgeted section inside a loop starts fresh each time it is entered.
Checkpoints check the budget independently of ordinary proof assertions.

See [checkpoints](../../examples/resource/memory/checkpoints.rs) and a
[checkpoint that fails](../../examples/resource/memory/expected-failures/checkpoint.rs).

## Giving different inputs different allowances

A conditional function budget can select its allowance from the inputs:

```rust
mem_peak <= mem_size(large)
    + if large { mem_size([u32; 8]) } else { mem_size([u32; 4]) },
```

Verus proves that the executed branch fits the selected allowance. Preconditions,
preceding proofs, and loop invariants can help establish this, including proving
that an expensive branch is unreachable. The verifier still determines the
storage charges automatically. See the [conditional example](../../examples/resource/memory/conditional.rs).

Currently, conditions support comparisons and Boolean operators over immutable
`bool` and all native integer inputs. Actual calls can also select allowances using
immutable scalar locals. Mutable selectors and expressions outside this subset
retain the conservative maximum. Argument-free `mem_peak(helper)` always uses
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
concrete structs, non-owning `Option` values, fixed-size boxes, boxed slices,
vectors with supported growth, and references/slices of supported non-owning values,
indexing, branches, while loops, and calls to checked functions in the same crate. Integer addition,
subtraction, multiplication, and signed negation retain Verus's overflow checks.
See the [integer example](../../examples/resource/memory/integers.rs).

`char`, floating-point types, other heap-owning types, destructors, enums other
than `Option`, generic structs, recursion, closures, and cross-crate calls are
not supported. Structs with ghost/tracked or reference fields are also
excluded. Destructuring outside supported Option patterns, casts, division, and
explicit `return`, `break`, or
`continue` also remain unsupported. An unsupported construct produces an error rather
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

Existing `mem_peak` clauses continue to bound total usage. Internally, budgets
pair a memory selection with a byte expression, and proof obligations project the
footprint onto that selection. Reports expose the same selection mechanism.
Source syntax for kind-specific clauses and device allocator models are not yet
provided. A helper or section with only a total contract may spend its unused
allowance in any kind; category queries conservatively retain that freedom rather
than inferring a category-specific promise from the current implementation.
