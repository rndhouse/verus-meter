# Memory contracts

Verus Meter verifies upper bounds on peak source-level memory for supported Rust programs. The [accounting policy](verus-meter/accounting/README.md) defines model bytes, their lifetimes, and how they combine.

## How do I read a contract?

- `resources peak(memory) <= bound` requires every allowed execution of the function or section to fit the bound. Ordinary Verus obligations, including bounds and overflow checks, still apply.
- In the [nested sections example](../examples/resource/memory/contracts/sections.rs), the function keeps an array, a section makes a copy, and an inner section makes scratch space. All three arrays are live at the peak.
- `assert(current(memory) <= bound)` checks what is live now. `assert(peak(memory) <= bound)` checks the peak so far. Both refer to the nearest budgeted section or function and currently require fixed bounds.

## How do I express a bound?

- `value_size(T)` measures inline storage. `ref_size(&T)` measures a reference. Both also accept binding names. `return_size(f)` measures the inline size of the declared result.
- `peak(f(args))` gives the declared allowance for those arguments. `peak(f)` gives the maximum declared allowance.
- Function budgets can use immutable scalar inputs, arithmetic, conditionals, and supported local spec helpers. Section budgets can also use executable locals and named slice or vector lengths. Budget arithmetic must fit in `u64`.
- A function marked `#[queryable_peak_memory]` can expose its allowance at runtime. Its caller still establishes the function's preconditions. [Runtime queries](../source/verus-meter/runtime/README.md)

## What can I verify today?

- Supported cases include concrete values, arrays, structs, options, boxes, vectors, boxed slices, selected loops, and safe nongeneric helpers in the same crate with an acyclic call graph. Support depends on the operation and the ownership facts available. [Executable examples](../examples/resource/memory/README.md)
- Local worker and ownership checks exist. A total concurrent peak still requires a global overlap proof. [Concurrent specification](verus-meter/concurrent-model.md)
