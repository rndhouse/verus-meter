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

The model measures declared storage using fixed sizes under a 64-bit policy.
Struct sizes add their fields without padding. `mem_size` follows these rules;
it does not report Rust's physical type layout. Native integers use their width
in bytes (`u8`/`i8`: 1, through `u128`/`i128`: 16); `usize` and `isize` both use 8.
Integer arrays multiply that size by their length.

- Parameters count throughout the call. Locals count from their declaration
  until their block ends, even after a move or last use.
- Initializing or assigning a value uses its destination's storage. An explicitly
  constructed array or struct without a destination counts once while evaluated.
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
already includes its parameters.

Using `mem_peak(helper)` lets a caller follow changes to the helper's contract.
It uses the declared allowance even when the helper currently needs less, so the
helper can change within that allowance. Both functions are checked independently.
For conditional helpers, actual calls use the allowance selected by their
arguments. A caller can write `mem_size(flag) + mem_peak(helper(flag))` to forward
that promise, or use a precondition to justify a smaller fixed bound.
See [calls](../../examples/resource/memory/calls.rs) and
[argument-specific budgets](../../examples/resource/memory/call_budgets.rs).

## Fixed-size heap objects

`Box<T>` can own one fixed-size value. `mem_size(Box<T>)` counts the owning handle
(8 model bytes); the live heap object adds `mem_size(T)` to `mem_peak`. A
`Box::new` initializer uses that object's storage, following the same destination
rule as local initialization. Allocator metadata, padding, and physical allocation
strategies are outside the model.

Moving a box between locals transfers its heap charge. Borrowing its contents
keeps that charge with the owner. Explicit `drop` or the owner's scope exit releases
the heap object; local variable slots still count until their own scopes end.
See [heap buffer reuse](../../examples/resource/memory/heap.rs) and
[two allocations that exceed their allowance](../../examples/resource/memory/expected-failures/heap_overlap.rs).

For now, boxes must stay within their function: helpers borrow their contents.
Box reassignment, nested boxes, owning struct fields, and custom destructors are
unsupported. Branches, loops, and budgeted sections may create and consume their
own boxes, but cannot move or drop owners from outside that region. Custom
allocator types remain unsupported.

## Vectors without growth

A local `Vec<T>` reserves storage once with `Vec::with_capacity(capacity)`.
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

The subset supports fixed-size non-owning elements, pushes, discarded pops,
length, indexing, and borrowing elements through `as_slice` or `as_mut_slice`.
Helpers take slices; owning or borrowed vector parameters, growth, reassignment,
and binding the `Option` returned by `pop` remain unsupported.

See [collecting selected numbers](../../examples/resource/memory/vectors.rs) and
[a push that requires growth](../../examples/resource/memory/expected-failures/vector_growth.rs).

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

Fixed budgets still account structurally for local storage, including unreachable
branches. Input-dependent call allowances are proved at the call site.

Sections and checkpoints require fixed bounds; constant call queries work in both.
Runtime allocation charges are also checked against these fixed bounds.
After a call with a conditional selector, checkpoints conservatively include the
callee's maximum allowance, even if a proof established a tighter bound at the call.

## Current scope

Checked functions must be safe, nongeneric, return `()`, and have a verified body.
The supported subset includes `bool`, all native integers, fixed integer arrays,
concrete structs, local fixed-size boxes and vectors without growth, supported
references and integer slices,
indexing, branches, while loops, and calls to checked functions in the same crate. Integer addition,
subtraction, multiplication, and signed negation retain Verus's overflow checks.
See the [integer example](../../examples/resource/memory/integers.rs).

`char`, floating-point types, other heap-owning types, destructors, enums, generic
structs, recursion, closures, cross-crate calls, and value-returning functions
are not supported. Structs with ghost/tracked or reference fields are also
excluded. Destructuring, casts, division, and explicit `return`, `break`, or
`continue` also remain unsupported. An unsupported construct produces an error rather
than silently receiving a zero cost.

A failure identifies the declaration, call, or checkpoint that cannot fit its
bound. The [array-copy example](../../examples/resource/memory/expected-failures/array_copy.rs)
shows a complete program deliberately rejected for exceeding its allowance.
