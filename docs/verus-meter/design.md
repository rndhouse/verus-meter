# Verus Meter

Resource contracts and verified cost bounds for Rust.

This document records the motivation, agreed scope, and exploratory directions for
a native Verus extension. It is a handoff for an agent to investigate the design
and recommend an implementation approach. No implementation or verified resource
analysis is claimed here. The syntax below is illustrative.

## Motivation

Verus makes it possible to specify functional behaviour and prove that an
implementation satisfies it. We want a similar workflow for resource usage:

> Under these preconditions, this implementation satisfies its functional
> specification and stays within this resource budget under the selected cost
> model.

A sorting function might promise both a sorted permutation and constant auxiliary
space. A change that introduces input-dependent temporary storage should require
changing that resource contract or should fail verification. This makes resource
requirements reviewable, compositional, and enforceable across code changes.

The initial discussion was inspired by a paper that verifies algorithmic query
complexity in Lean. Its relevant lesson is the separation between a cost model,
a bound stated in that model, and a proof that the algorithm meets the bound.
Verus Meter targets resource bounds on Rust implementations, initially local
storage, rather than adopting the paper's optimisation algorithms or drift analysis.

Heap allocation is comparatively straightforward to account for using controlled
allocation/deallocation APIs and trusted contracts. Local storage is the more
important design challenge here: declarations and temporary values do not
naturally pass through such APIs. We need the verifier to connect code to resource
accounting automatically.

## Scope and established preferences

The first focus is **algorithmic stack usage under a source-level cost model**.
Call this quantity *modelled local storage* when precision matters.

We want to build toward a finished feature integrated into Verus. An external
preprocessor or standalone proof of concept is not the desired development path.
A Verus fork is an acceptable development vehicle. Reuse Verus's proof machinery
and investigate how an upstreamable extension could be structured.

Prefer function clauses such as `requires`, `ensures`, and a possible `resources`
clause over an attribute-heavy interface. Attributes remain appropriate where
Verus already uses them, for example to identify a trusted external implementation.

Start the explanation and evaluation with **non-recursive code**. Recursion is a
later direction, not a prerequisite for demonstrating useful contracts.

Compiler-generated stack frames, LLVM transformations, machine instructions,
profiling, and physical RAM bounds are separate concerns. They must not dominate
or block this project. The initial guarantee is explicitly about the chosen
algorithmic model. There is no assumption that compilation preserves an exact
byte bound or introduces only constant overhead in every program.

## The contract we want

A useful initial example is in-place iterative insertion sort over an arbitrary
length mutable slice. It uses indices and a temporary element; it does not need
an auxiliary array proportional to the input length.

```rust
// Proposed interface, not currently supported syntax or verified code.
fn insertion_sort(values: &mut [u32])
    ensures
        sorted(final(values)),
        same_elements(final(values), old(values)),
    resources
        peak_local_storage_bytes <= INSERTION_SORT_WORKSPACE,
{
    let mut i: usize = 1;
    while i < values.len() {
        let key: u32 = values[i];
        let mut j: usize = i;

        while j > 0 && values[j - 1] > key {
            values[j] = values[j - 1];
            j -= 1;
        }

        values[j] = key;
        i += 1;
    }
}
```

`INSERTION_SORT_WORKSPACE` would be a constant determined by the model's charges
for the parameter, locals, expression temporaries, and relevant operations or
calls. It is independent of input length. Do not assign an exact value before
deciding those rules. Loop invariants and the functional proof are omitted.

`old(values)` denotes the entry state; `final(values)` describes the final value
behind the mutable borrow. These are specification mechanisms, not runtime copies.
See [Verus's mutable-reference documentation](https://verus-lang.github.io/verus/guide/mutable-references.html).

The input array already belongs to the caller. Passing a slice does not create a
second copy of its elements. The model may charge the slice descriptor as part of
the callee's local storage; it should not charge the backing array again.

A second concrete example could use `[u32; 64]` as scratch storage and accept at
most 64 elements. This is useful for checking a fixed byte budget. It is less
informative as an asymptotic example because its input domain is bounded.

The stack contract alone does not prohibit heap allocation. A function must not
be advertised as constant *total auxiliary space* solely because it satisfies a
local-storage contract. That stronger claim needs an additional heap contract or
an enforced allocation-free subset.

## Candidate local-storage semantics

The following is a starting proposal, not a settled design:

1. Charge each executable local storage slot by a model-defined type size.
2. Start its charge at a defined storage-creation event and retain it until the
   enclosing lexical scope exits.
3. Count the maximum simultaneously live charge, not the sum of all declarations
   executed over time.
4. Reuse storage on successive loop iterations after the iteration's scope exits.
5. Account for expression temporaries using explicit, documented lifetime rules.
6. Add the callee's resource requirement while the caller's local storage remains
   charged. Define argument and return-value handling to avoid accidental gaps
   or double counting.
7. Exclude specification and proof data, which are erased from execution.

Charging through lexical scope is intentionally conservative. We need not model
the earliest point at which a value becomes dead. Two arrays in separate nested
scopes can reuse the modelled budget; two simultaneously live arrays contribute
their sum. Conditional branches contribute the maximum feasible peak, not the
sum of both branches as though they executed simultaneously.

Define the unit explicitly. Possibilities include abstract storage cells or bytes
under a selected type-size policy. A byte policy must address `usize`, references,
arrays, tuples, structs, enums, alignment, and generics. Using a target's type
layout for a value's charge would still not claim to predict compiled stack frames.

Lexical scope is not a complete semantics by itself. Moves, partially initialised
locals, destructuring, shadowing, returned values, and temporary lifetime extension
need decisions. A conservative model can keep charging a moved-from slot until
scope exit; it must say that it is charging storage slots rather than live values.

## How verification would work

Verus Meter would automatically introduce internal accounting state and proof
obligations. Conceptually:

```rust
{
    // Generated verification operations, not user-written runtime code:
    reserve_local_storage(model_size_of::<[u32; 64]>());
    // Check that the resulting live total does not exceed the contract.

    let scratch = [0u32; 64];
    // Use scratch.

    release_local_storage(model_size_of::<[u32; 64]>());
}
```

This is an explanation of the accounting, not a requirement to literally insert
Rust function calls. The implementation could generate intermediate-representation
events and translate them directly into verification conditions.

For a call, a basic obligation is:

```text
caller_live_storage + callee_peak_requirement(arguments) <= caller_budget
```

This formula requires a precise convention for what the callee summary includes.
Non-recursive leaf functions should often admit automatic bound calculation.
Loops and more complex control flow may require resource invariants or inferred
summaries. A storage bound does not itself establish termination: a loop can run
forever while reusing constant storage. Keep termination obligations separate.

The accounting must not be something the user can bypass by omitting a manual
charge, resetting a counter, or inventing a release. Instrumentation and resource
state should be controlled by the verifier. `Tracked` types could support resource
APIs, but ownership-checked ghost state alone does not establish that all local
storage has been counted.

## Where changes are likely to live

The proposed architecture follows Verus's existing pipeline; exact insertion
points need source inspection against a pinned revision. The
[architecture overview](https://github.com/verus-lang/verus/blob/main/source/CODE.md)
identifies these components:

| Component | Proposed responsibility |
|---|---|
| Syntax parser and `builtin_macros` | Parse and lower resource clauses. |
| `rust_verify` | Extract contracts and preserve typed source storage events. |
| `vir` | Represent contracts and events; generate accounting and call obligations. |
| Existing AIR/SMT pipeline | Discharge the resulting arithmetic and logical obligations. |
| `vstd` | Provide resource definitions, supporting lemmas, and library contracts. |
| Tests and diagnostics | Detect omissions and report budget failures at useful source locations. |

The central design question is where storage semantics should be attached.
[VIR-AST](https://github.com/verus-lang/verus/blob/main/source/vir/src/ast.rs)
intentionally omits some Rust details, while
[AST-to-SST lowering](https://github.com/verus-lang/verus/blob/main/source/vir/src/ast_to_sst.rs)
introduces verification temporaries. Counting all locals in an arbitrary late
representation would therefore need justification. Preserve the distinction
between source execution events and verifier-generated bookkeeping.

Investigate a typed source-to-VIR event capture stage plus a dedicated accounting
pass. This is a candidate, not a mandated architecture. If necessary information
is unavailable there, identify another rustc representation that supplies it while
keeping the cost model source-oriented. LLVM changes are outside the intended scope.

## Requirements for a finished feature

Resource verification should cover all supported constructs and reject unsupported
resource behaviour explicitly. It must not silently assign zero cost to a call
because its implementation or resource contract is unavailable.

Function summaries need to compose across modules and crates. Trait methods,
generic functions, closures, indirect calls, and external implementations need a
policy: verified summaries, explicit trusted contracts, or rejection in a
resource-checked context. Exported contracts should identify the cost model so
incompatible assumptions cannot silently mix.

The model also needs a clear treatment of scope exits: ordinary completion,
`return`, `break`, `continue`, and, where supported, unwinding and destructor calls.
Unsupported exits may be rejected initially, but the limitation should be explicit.

Diagnostics should identify the declaration or call responsible for exceeding
the budget and show the relevant live total. Tests should cover passing programs
and deliberate violations, especially cases where incomplete instrumentation
would incorrectly accept a program.

## Exploratory directions

These questions should guide investigation rather than be taken as settled choices:

- **Cost semantics:** Is a lexical-slot model useful and predictable enough? How
  should expression temporaries be represented? Can a small formal semantics
  state precisely what peak local storage means?
- **Instrumentation correctness:** What argument establishes that every execution
  event in that semantics is represented by the generated accounting? Identify
  which parts are trusted implementation code and which could have checked proofs.
- **Exact versus asymptotic contracts:** Start with concrete symbolic upper bounds
  from which constant or linear space follows. Investigate whether explicit
  asymptotic syntax adds value and how its constants and domains would be defined.
- **Automatic inference:** Can Verus calculate a summary for simple functions and
  check it against the user's budget? How much annotation is needed for loops?
- **Call composition:** Can bounds be expressed in terms of argument values,
  generic type sizes, or existing functional preconditions without inspecting
  callees at every call site?
- **Precision:** Would later lifetime-based release improve useful bounds without
  making specifications depend on unstable implementation details?
- **Recursion:** Once non-recursive contracts are established, investigate peak
  storage over active calls and its relationship to termination measures.
- **Other resources:** Could the event/contract infrastructure support heap usage
  or operation counts later? Keep their different semantics explicit: storage can
  be released; executed operations accumulate.

## Requested next investigation

Inspect Verus's current implementation and recommend an integrated design. The
desired output is a technically grounded proposal, not an external prototype or
an assumption that the illustrative syntax already exists.

Please determine:

1. A precise first cost model and supported Rust subset with useful real examples.
2. Where required type, scope, temporary, and call information is available, and
   where it is lost or transformed in Verus.
3. The minimal coherent changes to parsing, internal representations, accounting,
   exported contracts, and verification-condition generation.
4. A compositional contract design and explicit treatment of unknown callees.
5. The soundness argument, trusted assumptions, and tests most likely to expose
   missed charges or incorrect releases.
6. A sequence of implementation milestones inside Verus that leads toward the
   finished feature, including important risks and unresolved design choices.

The existing heap-oriented discussion sketch is available at
[/home/user/dev/paper-reading-group/fv-performance-optimisation/memory-resource-contract-example.md](/home/user/dev/paper-reading-group/fv-performance-optimisation/memory-resource-contract-example.md).
It is background only; stack/local-storage accounting is the focus of this project.
