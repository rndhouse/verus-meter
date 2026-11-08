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
using the function's preconditions. Arbitrary spec expressions and named numeric
constants are not yet supported as budget operands.

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

Box reassignment, nested boxes, owning struct fields, and custom destructors are
unsupported. Branches, loops, and budgeted sections may create and consume their
own boxes, but cannot move or drop owners from outside that region. Custom
allocator types remain unsupported.

## Vectors without growth

A `Vec<T>` reserves storage once with `Vec::with_capacity(capacity)`.
Its handle costs `mem_size(Vec<T>)` (24 model bytes), and its backing storage
costs `capacity * mem_size(T)`, even when empty. The requested capacity is the
model's limit; allocator over-allocation is outside the guarantee.

Each `push` must be proved to fit that reservation. Branch conditions and loop
invariants can establish this. `pop` makes room for another element but retains
the backing storage. Moves transfer the reservation; dropping releases it.
The same ownership restrictions as boxes apply across branches, loops and sections.

Capacity can be a literal or an immutable unsigned variable. Function budgets
can use an input directly, for example `mem_size(capacity) + mem_size(Vec<u32>)
+ capacity * mem_size(u32)`. Callers use `mem_peak(helper(arguments))` to compose
runtime formulas; an argument-free query requires a fixed envelope.

The subset supports fixed-size non-owning elements, pushes, pops returning `Option<T>`,
length, indexing, and borrowing elements through `as_slice` or `as_mut_slice`.
Helpers can take ownership or borrow slices of the elements. Pushes into an incoming
vector need a capacity contract, which is not yet supported. Borrowed vector
parameters, growth, and reassignment also remain unsupported.

See [collecting selected numbers](../../examples/resource/memory/vectors.rs) and
[a push that requires growth](../../examples/resource/memory/expected-failures/vector_growth.rs).

## Passing heap ownership between helpers

Helpers can consume or return a `Box<T>` or `Vec<T>`. The helper's budget covers
its handles and additional storage. Checked lifetime summaries tell callers
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
returns and owners inside structs or `Option` remain unsupported.

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
concrete structs, non-owning `Option` values, fixed-size boxes and vectors
without growth, supported
references and integer slices,
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
