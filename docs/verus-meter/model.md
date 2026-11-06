# Current resource model: lexical-slots-v5-64

This is the authoritative description of the implemented storage model. The
[design](design.md) describes the broader project; the experiment documents
record earlier milestones and their validation results.

The checker enforces a structural upper bound on storage in its source-level model.
It counts **model bytes**, using a fixed abstract 64-bit policy. It does not
predict physical stack frames, target ABI layout, register allocation, compiler
copy elision, or heap consumption. Storage objects are local variables, parameters,
and aggregate values explicitly constructed without a destination. Evaluating a
literal, read, operator, index, or borrow introduces no extra storage object.
This is a model definition, not an assumption about compiler behavior.
Unsupported executable constructs fail closed.

## Contract and supported subset

```rust
fn example()
    resources peak_memory_bytes
        <= memory_budget::<[u32; 64]>(),
{
    { let first = [0u32; 64]; }
    { let second = [0u32; 64]; }
}
```

The resource clause comes after the other function clauses. Its budget is a
compile-time expression built from nonnegative `u64` literals (unsuffixed or
suffixed `u64`), `memory_budget` queries, addition, multiplication, and parentheses:

- `memory_budget(buffer)` queries the model size of the named value's type.
  An `&mut SortBuffer` parameter costs 8 bytes; it excludes the backing struct.
- `memory_budget(sorting::insertion_sort)` queries the function's **declared**
  budget, including any slack. Function paths and import aliases use resolved
  Rust identities. Only eligible annotated functions in the same crate qualify.
- `memory_budget::<SortBuffer>()` queries a type directly, including when the
  local value does not yet exist at the function's signature. It uses the same
  unpadded layout rules as executable storage accounting.

For example, the struct helper declares:

```rust
resources peak_memory_bytes
    <= memory_budget(buffer) + memory_budget(sorting::insertion_sort),
```

The queries are erased metadata: they do not evaluate, copy, or move their
arguments, and add no runtime storage. The argument must be a name/path, not
a field access or computed expression. Runtime arithmetic, arbitrary function
calls, named numeric constants as budget operands, subtraction, and generic
function references are unsupported. Every sum and product must fit in `u64`.

Budget references form their own acyclic graph, independent of executable calls.
Self/mutual references are rejected even under multiplication by zero. Changing
a referenced bound or type layout recomputes dependent budgets; every annotated
body is still checked against its resulting bound. A formula is not itself a
proof: construction, argument handoff, or other execution can exceed it.

Functions without a resource clause continue through normal Verus verification
without resource checking. The former `peak_local_storage_bytes` spelling is
replaced by `peak_memory_bytes`. Version 5 removes inferred expression and address
temporaries consistently across initialization, assignment, and calls.

Annotated functions must be safe, nongeneric executable functions with a checked
body and unit return type. Async functions, external bodies, specification
proxies, and trait-method forms are rejected. Supported constructs include named
bindings, scalar/array values, concrete structs, supported references, arithmetic and comparisons,
indexing, assignments, unit-valued blocks and branches, while loops, and direct
calls to annotated functions in the same crate.

Enums/unions, heap-owning values, destructors, general nested references, closures,
custom indexing, casts, division, shifts, destructuring/wildcard bindings,
`let-else`, value-returning blocks/functions, and explicit `return`, `break`, and
`continue` remain unsupported. Borrowing temporary backing storage is rejected.
Calls with generic/dynamic targets, imported callees, and recursive call graphs
are also rejected. Supporting a construct in Verus does not automatically give
it a resource rule.

## Sizes

| Value | Model bytes |
| --- | ---: |
| `bool` | 1 |
| `u32` | 4 |
| `usize` | 8 |
| `[u32; N]`, with a concrete constant length | `4 * N` |
| Supported concrete struct | Sum of its field sizes, without padding |
| Reference to a supported sized value | 8 |
| `&[u32]` or `&mut [u32]` | 16 |
| Unit | 0 |

Arrays contain `u32` elements in this subset. Unsized slices are accessed through
references, not charged as standalone values. A reference excludes its pointee:
a local backing array retains its own charge, while a caller-owned array is not
charged again inside the callee. Copying a borrowed array into a local charges
the new local slot, without a separate read result or address scratch.
Unsupported pointee types and nested reference values are rejected, apart from
the narrow compiler adapter described below. Size multiplication and total
additions are checked for overflow.

## Concrete structs

Local, nonopaque, nongeneric structs may contain `bool`, `u32`, `usize`, unit,
fixed `u32` arrays, and other supported concrete structs. Named, tuple, and unit
struct forms are supported. Instantiating a generic struct with concrete type
arguments does not yet qualify. Reference/decorated fields, ghost/tracked fields,
type invariants, external type proxies, imported layouts, and destructors are
rejected, including destructors nested inside fields. Field validation ensures
every supported layout is fixed-size; recursive layout traversal is rejected.

The model sums field sizes with checked arithmetic and excludes ABI alignment
and padding. Thus `{ values: [u32; 8], ready: bool }` occupies 33 model bytes.
Rust-to-VIR preserves whether a datatype actually is a struct: a single-variant
enum or single-field union is not accepted merely because its VIR shape is similar.

Initializers of every supported type use the destination's existing storage.
Fields occupy storage within the enclosing struct; nested constructors do not
add a separate result. Literals, field reads, and computations add no implicit
slots. Fields and array literal elements are evaluated in source order; a repeat
operand is checked even for a zero-length array. Struct update syntax (`..base`)
remains unsupported.

For example, `let a = [0u32; 64]; let b = [0u32; 64];` charges exactly two arrays.
A struct containing an array charges only its field layout. Explicitly writing
`let values = [...]; let buffer = Buffer { values, ... };` introduces a separate
local: both the array local and the struct remain charged to scope exit.
Likewise, `let fill = 0u32; let a = [fill; 64];` counts the named scalar as well
as the array, while `let a = [0u32; 64];` counts only the array.

Copies and moves into a destination count the source and destination slots;
they do not add a transfer object. Even a moved source stays charged to lexical
scope exit. No implicit destructor execution needs accounting for supported
types. The same destination rule applies to parameters and assignments,
including assignment to a previously uninitialized local.

An aggregate expression without a destination, such as `[0u32; 64];`, has one
result charge while its contents are evaluated. Nested fields share that result's
storage. Discarded scalar expressions introduce no storage objects.

Field access, indexing, and borrowing use existing storage without new address
or descriptor temporaries. A reference bound to a local or parameter still
occupies its slot. Temporary backing structs and field access through temporary
struct values remain unsupported.

## Lifetimes and expression evaluation

- Executable parameter slots are reserved at function entry and released at exit.
- Each executable local slot is reserved before its initializer and retained to
  lexical block exit. Uninitialized locals are charged, and shadowing does not
  release the previous slot. Reading, copying, or moving a local does not release it.
- Literals and operators do not reserve inferred evaluation temporaries. A result
  assigned to a local, field, or parameter uses that destination's storage.
  Arithmetic supports checked `+`, `-`, and `*` on `u32` and `usize`;
  ordinary Verus overflow checks still apply.
- Standalone aggregate expressions reserve one result, released when consumed.
  Initializers and nested fields share the destination's storage instead.
- Unit-valued blocks release local slots in reverse declaration order and restore
  their entry live total.
- Mode-checked ghost declarations, proof blocks, and proof assertions are erased
  and contribute no charge. They do not supply storage-budget proofs.

Conditions are checked before their branch or loop body. Both branch alternatives
are analyzed from the same entry total and their peaks are maximized.
Short-circuit boolean operations visit both possible sides. Constant conditions
and functional preconditions do not prune paths in this analysis.

A while loop is analyzed for one condition/body iteration whose net charge must
be zero, so iterations reuse storage. This structural rule establishes no
termination property; functional termination verification remains separate.

## Places, indexing, and assignment

Named locations, dereferences, field projections, and indexing add no synthetic
address storage. The checker still validates the base, pointee type, index, and
coercion shape, and visits executable index expressions. Verus still checks
bounds and lifetimes. General nested references and borrowed backing temporaries
remain unsupported.

Assignment checks the RHS before the destination address. All supported results
use the destination's existing slot. Compound `+=`, `-=`, and `*=` add no
extra old-value or result objects. Self-referential assignments follow the same
source-level rule without making claims about physical in-place execution.

Borrowing and reborrowing add no anonymous descriptor charges. A reference
stored in a local or passed as a parameter is counted as that slot; backing
locals retain their lexical lifetimes independently of their references.

## Resource intrinsics

Three compiler-identified operations have rules in the model:

| Intrinsic | Recognition | Accounting |
| --- | --- | --- |
| Array repeat | Source `[value; length]` syntax | One destination/result; operand checked, without an implicit fill slot |
| Slice length | Resolved rustc `slice_len_fn` language item | Receiver checked; result uses its destination |
| Array-to-slice coercion | Compiler-inserted reference unsizing | Backing data remains owned; reference uses its destination |

These operations do not add a separate callee frame. Rust-to-VIR records their
provenance in `Option<ResourceIntrinsic>`, which admits at most one intrinsic per
call; autospec processing preserves it. Explicit calls to array helpers do not
receive the syntax exemption, and a user method named `len` is not an intrinsic.

Coercions support `&[u32; N]` to `&[u32]` and `&mut [u32; N]` to `&mut [u32]`.
The checker recognizes the narrow compiler adapter used for shared unsizing,
which may contain `&&[u32; N]`, without charging synthetic descriptors. The inner
reference is validated normally: this does not enable borrowed backing
temporaries or general nested-reference values.

## Direct calls

Every ordinary callee must have a current-model contract and an eligible checked
body in the same crate. Let `L` be the caller storage already live before a call,
`P` all executable parameter-slot storage, and `B` the callee's **declared**
budget, which includes its parameters.

1. Visit executable arguments left to right. Reserve each parameter slot just
   before evaluating its initializer. Earlier parameters stay live during later
   argument evaluation; later parameters are not reserved yet. Erased arguments
   contribute no storage.
2. Argument initialization uses the parameter's storage for all supported types,
   without a separate argument-result charge.
3. After initialization, account for execution at `L + B` by reserving only
   `B - P` additional bytes. Reject a declared budget smaller than `P`.
4. Release the callee's storage on its unit-valued return. Caller storage remains live.

The peak is the maximum of argument-evaluation peaks and `L + B`. Nested calls
during argument evaluation include any previously reserved parameters.
Sequential calls reuse callee storage. Passing a named value counts the caller's
slot and the callee's parameter; passing a reference retains the backing data
with its owner. The declared bound is used even if the body needs less, allowing
implementation changes within that contract.

Every annotated local body is checked before accepting the crate, including
callees declared after callers and calls inside unreachable branches. Executable
call edges must form an acyclic graph. Self-recursion and mutual recursion are
rejected even at zero storage cost, preventing circular justification of bounds.

## Cost policy review

The implementation has only four sources of positive charges: local slots,
parameter slots, standalone aggregate results, and the additional part of a
callee's declared budget. Expression evaluation and place access do not reserve
storage. A callee's parameters are included in its budget, not added twice.

The remaining choices are definitions of this model, rather than conclusions
about how a compiler stores values:

| Policy | Meaning and consequence |
| --- | --- |
| Fixed sizes | `bool` is 1, `u32` is 4, and a model word is 8 bytes. These are explicit units of account. |
| References | A sized reference occupies one word; a slice reference occupies two. Neither includes its pointee. Two references to the same array do not duplicate the array's charge. |
| Structs and arrays | Sum the contained values, with no ABI padding. Unit and empty aggregates occupy zero model bytes; a reference to one still occupies a reference slot. |
| Lexical lifetimes | A declaration reserves a slot until its block ends, including unused, uninitialized, shadowed, or moved-from slots. This measures declared storage, not the number of currently initialized values. Explicit scopes permit reuse. |
| Initialization | The destination is reserved while its initializer runs. A helper called during initialization therefore overlaps that destination. |
| Calls | Caller-owned storage remains live. Each parameter has one slot; the callee's declared budget includes it. Declared slack is intentionally retained for compositional contracts. |
| Control flow | Alternative branches use a maximum, and iterations reuse their block's storage. Unreachable branches still contribute to the structural bound. |
| Standalone aggregates | An explicitly written aggregate expression without a destination owns one temporary result. Scalar expression evaluation has no storage charge. This is a deliberate distinction in the current object model. |

The most consequential lifetime choice is charging moved-from slots until scope
exit. For example, moving a non-Copy struct through three local bindings charges
three declared slots, even though only the last binding still owns the value.
Releasing slots at a move or last use would be a different, ownership/liveness
model; it is not currently inferred from compiler behavior.

The bound is therefore a structural upper bound under these rules, not an exact
runtime peak. The backing data behind input references is outside the callee's
own charge. Unsupported heap-owning types, destructors, and unknown calls are
rejected rather than treated as free.

## Compiler integration and trust boundary

The parser recognizes the clause; `builtin_macros` lowers it to an erased verifier
builtin; typed Rust-to-VIR lowering resolves query arguments without evaluating
them, and header extraction stores the budget expression in function attributes. The checker
runs once local functions have passed mode checking, before resolution inference
or AST simplification rewrites temporary places, and before exporting the crate.

It computes structural bounds directly using checked arithmetic, without an SMT
counter or reliance on user assertions. Standalone aggregate expressions leave
their result charged; other expressions add no inferred slots. Completed blocks
restore their entry total. Source spans identify reservations,
releases, and the first maximum in traces and budget errors. Branch traces show
analyzed alternatives, not a single runtime execution.

The checker implementation, type/mode translation, provenance, and erasure rules
are trusted. There is no machine-checked proof of the instrumentation itself.
Normal Verus functional, lifetime, bounds, and overflow checks remain active;
proof assumptions and verification-skipping flags retain their usual meaning.

The serialized `ResourceContract` variant identifies the cost model. Earlier
variants keep their discriminants and are rejected rather than reinterpreted.
Current clauses select the expression-bearing v5 variant. Earlier contracts are
rejected because their accounting rules differ. Type sizes remain unchanged. Rebuild vstd/dependencies as described
in [setup.md](setup.md) after updating the verifier.
Serialized metadata is specific to this fork, not a stable interchange format.

## Source organisation

The public entry point remains `vir::resource_storage::check_crate`; contract and
report types are re-exported from that module. Its implementation is divided by
responsibility:

| File | Responsibility |
| --- | --- |
| [mod.rs](../../source/vir/src/resource_storage/mod.rs) | Crate orchestration and call-cycle rejection |
| [model.rs](../../source/vir/src/resource_storage/model.rs) | Model identity, word size, supported arithmetic and function eligibility |
| [budget.rs](../../source/vir/src/resource_storage/budget.rs) | Checked budget arithmetic, resolved function references, and budget-cycle rejection |
| [layout.rs](../../source/vir/src/resource_storage/layout.rs) | Type sizes, concrete struct eligibility, field layouts and recursive layout checks |
| [accounting.rs](../../source/vir/src/resource_storage/accounting.rs) | Private live/peak state, checked reservations/releases, trace events, budget diagnostics |
| [analysis.rs](../../source/vir/src/resource_storage/analysis.rs) | Function entry, expression traversal, lexical scopes and control flow |
| [places.rs](../../source/vir/src/resource_storage/places.rs) | Source-place validation, reads and borrows |
| [construction.rs](../../source/vir/src/resource_storage/construction.rs) | Aggregate destinations, nested construction, copies and moves |
| [calls.rs](../../source/vir/src/resource_storage/calls.rs) | Argument handoff, callee budgets and intrinsic evaluation |

Syntax/header changes stay in the existing parser and compiler layers;
`rust_verify/src/resource_budget.rs` handles typed budget expressions. Intrinsic
provenance is declared with `CallTargetAttrs` in `vir/src/ast.rs` and set during
Rust-to-VIR lowering. The checker has no dependency on rustc internals.

## Examples and checks

| Example | Expected model peak |
| --- | --- |
| [Lexical reuse](../../examples/resource_storage.rs) | 256 for separate 64-element array scopes; 512 when overlapping |
| [Insertion sort](../../examples/resource_insertion_sort.rs) | 44, independent of slice length |
| [Complete call chain](../../examples/resource_calls.rs) | 76: a 32-byte local array plus the sorter's 44 |
| [Struct field sorting](../../examples/resource_structs.rs) | 85: a 33-byte struct plus its helper's 52 |
| [Keeping an array copy (expected failure)](../../examples/expected-failures/resource_array_copy.rs) | Rejected: peak 32 exceeds the declared budget of 16 |

Use the development environment in [setup.md](setup.md). From `source`:

```sh
cargo build --release -p rust_verify
VERUS_Z3_PATH="$PWD/z3" ./target-verus/release/verus ../examples/resource_calls.rs --trace --compile -o target-verus/resource-calls
./target-verus/resource-calls
cargo test --release -p rust_verify_test --test resource_storage --test resource_storage_slices --test resource_storage_calls --test resource_storage_structs --test resource_storage_budgets --test resource_storage_initialization --test resource_storage_model
```

The integration suites are grouped into basic storage, slices/arithmetic,
call composition, structs, symbolic budgets, and aggregate initialization.
Build the verifier before testing: the test harness invokes the existing executable. Representation changes also require the installed
verifier/vstd rebuild from the setup instructions.

## Seeing a memory contract reject a regression

[resource_array_copy.rs](../../examples/expected-failures/resource_array_copy.rs)
is intentionally failing code. It edits a copy of an array while preserving the
original, but its contract allows room for only one array. Both arrays coexist,
so making the copy exceeds the budget.

Comments mark the violated contract and the copy declaration where Verus reports
the violation. The file contains only
this failing version; the test does not rewrite its source.

From `source`, using the environment in [setup.md](setup.md), run Verus directly
to see the rejection (a nonzero exit status is expected):

```sh
VERUS_Z3_PATH="$PWD/z3" ./target-verus/release/verus ../examples/expected-failures/resource_array_copy.rs
```

The expected diagnostic is:

```text
local storage budget exceeded: peak 32 bytes exceeds budget 16 bytes (lexical-slots-v5-64)
```

The companion [resource_array_copy test](../../source/rust_verify_test/tests/resource_array_copy.rs)
verifies that file exactly as written and asserts the specific memory diagnostic:

```sh
cargo test --release -p rust_verify_test --test resource_array_copy -- --nocapture
```

That test passes when the example is rejected for exceeding its memory budget.
Accepting the example, or rejecting it for a different reason, fails the test.
The file is also marked `expect-errors` for the general examples test runner.

## Refactor validation (v2)

The organisational refactor was validated on 2026-11-06 without changing the
v2 accounting rules or existing test expectations:

- The release workspace and installed verifier built successfully; rebuilt vstd
  reported 2,226 verified and zero errors.
- All 93 resource tests and 373 selected upstream regression tests passed;
  five upstream tests were ignored. The complete upstream suite was not run.
- All three examples verified, compiled, and ran. Their reserve/release messages,
  live totals, peak/budget reports, and verification-result lines exactly matched
  traces captured before the refactor.
- Workspace formatting, `git diff --check`, and local documentation links passed.

## Struct validation (v3)

Validated locally on 2026-11-06:

- Release workspace and installed verifier builds passed. Rebuilt vstd reported
  2,226 verified and zero errors after adding struct-kind metadata.
- All 128 resource tests passed: the previous 93 plus 35 struct tests covering
  layouts without padding, constructors, copies/moves, field reads/writes/borrows,
  nested structs, call handoff, exact/insufficient budgets, and rejection cases.
- 873 selected existing tests passed, with eight upstream-ignored tests, across
  `basic`, `functions`, `loops`, `size_of`, `mut_refs_slices_arrays`, `arrays`,
  `erase`, `modes`, `structural`, `unions`, `mut_refs_unions`,
  `user_defined_type_invariants`, `traits`, and `mut_refs`. The complete upstream
  suite was not run.
- The struct example reported eight verified checks and zero errors, compiled,
  and ran. Its trace reported 84 for insertion sort, 92 for `sort_buffer`, and
  125 for both the owning caller and `main`. A budget of 124 fails, and adding
  a `u32` field raises the required bound to 129.
- A local compiled harness checked all 6,561 eight-element arrays over three
  values, plus an extreme-value case. All 6,562 cases matched Rust's sort and
  set `ready` to true. Only the harness was excluded from verification; the
  sorter, struct helper, and example call chain were verified before compilation.
- Workspace formatting, `git diff --check`, and local documentation links passed.

## Symbolic budget validation (v3)

Validated locally on 2026-11-06 without changing the accounting rules:

- The release workspace and installed verifier built successfully; rebuilt vstd
  reported 2,226 verified and zero errors.
- All 148 resource tests passed, including 20 dedicated budget-expression tests.
  They cover type/value queries, non-Copy parameters, qualified names and aliases,
  declared slack, checked arithmetic, independent budget cycles, and rejection
  of unsupported contracts and types.
- All five resource parser tests passed. The same 873 selected upstream tests
  listed above passed, with eight upstream-ignored tests.
- All four examples verified, compiled, and ran with unchanged peak bounds.
  Adding a field to the struct example now updates its type-derived budget
  automatically; freezing that contribution at 33 still fails at 129 versus 125.
  Lowering the sorter or either owning caller's budget by one byte still fails.

## Destination accounting validation (v4)

Version 4 replaces the duplicate aggregate-initializer charge with the
destination rule. The earlier validation sections describe historical models.

- The release workspace and installed verifier built successfully. Rebuilt vstd
  reported 2,226 verified and zero errors.
- All 168 resource tests passed, including 20 initialization tests. These cover
  exact and one-byte-short bounds for repeat/literal arrays, nested structs,
  explicit intermediates, copies, delayed initialization, reassignment,
  self-referential assignment, and mixed scalar/aggregate call arguments.
- The same 873 selected upstream regression tests passed, with eight
  upstream-ignored tests. The complete upstream suite was not run.
- All four examples verified, compiled, and ran. Lexical reuse now peaks at 260,
  overlap at 516, and branches/loops at 261. The sorting examples retain their
  previous peaks because calls determine their maximum.
- Standalone examples express their own storage needs. Function-budget references
  in the examples now correspond to actual helper calls.

## Source-object accounting validation (v5)

Version 5 removes inferred scalar results, operand copies, address scratch,
borrow descriptors, and argument-transfer objects. Initializers of every
supported type share their destination's charge. Earlier validation sections
record historical models.

- The release workspace and installed verifier built successfully. Rebuilt vstd
  reported 2,226 verified and zero errors.
- All 176 resource tests passed. Initialization tests now cover literals with
  zero storage, explicit scalar intermediates, computed initializers, nested
  calls during parameter initialization, and exact/one-byte-short object bounds.
  Overflow checks, unsupported-type rejection, and functional proofs remain active.
- The same 873 selected upstream tests passed, with eight upstream-ignored tests.
  The complete upstream suite was not run.
- All four examples verified, compiled, and ran. Lexical reuse peaks at 256,
  overlapping arrays at 512, and branches/loops at 257. Insertion sort peaks at
  44, its array caller at 76, and the struct example at 85.
- Each example's comments and budget expressions describe source storage.
  The sorter's scalar contribution is its explicitly declared saved element;
  literal array initializers have no separate fill-value charge.


## Cost policy audit validation (v5)

The cost-policy review changed no accounting rules. Ten additional boundary
tests passed in `resource_storage_model`, checking exact bounds and rejection
one byte below each bound. They cover the fixed size table, shared backing data,
reference scopes, moves, repeated iterations, unreachable branches, standalone
aggregates, references to zero-sized values, and nested initializer calls.
