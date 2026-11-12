# Memory contracts

Verus Meter proves upper bounds on peak memory for a supported subset of Rust.
Use the [executable examples](../../examples/resource/memory/README.md) to learn
contract syntax, heap ownership, loops, and expected failures.

## Contracts and queries

- `resources peak(memory) <= bound` limits the maximum memory live at once in a
  function or budgeted section. Functions without a resource clause receive only
  ordinary Verus verification.
- `value_size(T)` measures inline storage, excluding separate allocations;
  `ref_size(&T)` measures a reference, excluding its pointee. Both also accept
  binding names.
- `peak(helper(arguments))` queries the helper's declared allowance for those
  arguments, without executing it. `peak(helper)` takes its maximum allowance.
- `assert(peak(memory) <= bound)` checks the peak so far;
  `assert(current(memory) <= bound)` checks storage still live. Both refer to the
  nearest budgeted section or function.

Function budgets can depend on immutable scalar inputs and use arithmetic,
conditionals, and local verified numeric specification functions. Budget
arithmetic must fit in `u64`; sections and checkpoints currently require fixed
bounds. See [contract examples](../../examples/resource/memory/README.md#contracts).

## What the guarantee covers

The model counts source values and separately owned allocations using a fixed
64-bit size policy. It does not measure the compiled program's physical stack,
allocator overhead, fragmentation, or resident memory. Struct sizes add their
fields without ABI padding; ghost and proof state contribute no runtime storage.

- Parameters, local slots, owning handles, and modeled temporaries count while
  live. Moves transfer ownership; copies require additional storage. Scope exit
  and explicit drop release storage; last use alone does not.
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

## Supported boundary

Supported building blocks include native integers, fixed integer arrays,
concrete nongeneric structs, `Option`, `Box<T>`, `Vec<T>`, and `Box<[T]>` with
supported layouts and operations. Nested ownership composes through fixed fields
and runtime collections. Checked calls currently require safe, nongeneric,
verified functions in the same crate and an acyclic call graph.

Supported loops include counted while/unconditional loops, representable exits,
and finite half-open integer for ranges with supported `rev`, `skip`, and `take`
adapters. Exact ownership summaries support selected conditional effects, child
transfers, and indexed updates. This does not cover arbitrary data-dependent
progress, partial exits, or all iterator APIs. A local peak proof can succeed
while exporting caller-visible ownership remains unsupported.

Other owning containers, shared ownership, custom destructors, recursion,
generic layouts, and cross-crate resource summaries remain unsupported. Examples
illustrate supported programs rather than promise every operation on their types.
See [heap and loop examples](../../examples/resource/memory/README.md#heap).

Internally, charges distinguish `host.local` and `host.heap`. Current source
contracts bound total `memory`; separate kind-specific limits and GPU allocator
models are not yet provided.
