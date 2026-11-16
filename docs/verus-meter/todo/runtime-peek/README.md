# Queryable peak-memory bounds

`#[queryable_peak_memory]` lets an application evaluate a function's
declared peak-memory allowance for concrete arguments before deciding to run it.
The authoritative formula remains `resources peak(memory) <= expression`.
Retain that formula as data and evaluate it with a shared runtime interpreter;
generate typed query wrappers, not a separate arithmetic implementation per bound.

These documents record the implementation plan and completed task boundaries.
Maintain the authoritative task documents in the primary checkout under
`docs/verus-meter/todo/runtime-peek/`. Implementation commits are recorded in the
completed task documents.
Keep instructions and references repository-relative so the plan survives relocation.

1. [Working prototype](complete/01-working-prototype.md) — complete
2. [Runtime expressions and evaluator](complete/02-runtime-evaluator.md) — complete
3. [Additional expressions and spec helpers](complete/03-expression-support.md) — complete
4. [Attribute and executable queries](complete/04-attribute-and-queries.md) — complete
5. [Correctness tests and regressions](complete/05-tests-and-regressions.md) — complete
6. [User example and integration validation](complete/06-example-and-validation.md) — complete

## Completing tasks

After a task's implementation and required validation are complete, update its
checkboxes and move its numbered document into `complete/` in the primary
checkout. Update this index and every link to the moved document, and adjust
relative references inside it for the extra directory level. Keep this README
at the top level. Commit the documentation updates as well as the implementation
changes in their respective checkouts; do not mark work complete from a planning
or experimental result alone.

## First-version boundary

Task 1 delivers a small working path from a resource clause to a callable query
and budget comparison. Start the user example there and grow it through later
tasks. Expand the evaluator and expression coverage after the compilation path
works; settle interface details as the implementation supplies evidence.

- Opt in on verified, safe, nongeneric free functions with supported scalar inputs.
  Target `foo::peak_memory_bound(...)`, with argument types matching `foo`.
- Support constants, numeric inputs, addition, multiplication, comparisons,
  Boolean operations, conditionals, model-size queries, and simple local numeric
  spec helpers reducible to these operations. Preserve supported casts to
  mathematical integers and local bindings needed by those helpers.
- Use arbitrary-precision arithmetic internally. Expose model bytes through a
  small public API that supports budget comparisons without leaking a third-party
  integer type. Task 1 establishes a minimal interface; task 2 settles the numeric
  result and error API. Checked native arithmetic is acceptable for the narrowly
  bounded task-1 experiment, with arbitrary precision required by task 2.
- Reject unsupported queried expressions during compilation. Existing resource
  contracts without the attribute retain their current supported scope.
- Defer recursion, functions returning functions, collection-dependent specs,
  generic or method interfaces, cross-crate resource summaries, OS memory discovery,
  memory reservation, and additional resource metrics.

The query returns a declared upper bound, not measured usage or a necessary minimum.
Execution guarantees remain conditional on the function's preconditions. A failed
budget comparison does not prove that execution cannot fit. The current abstract
memory model remains authoritative; this feature does not establish correspondence
with available physical RAM. The query's own allocation and execution costs are
separate from the queried function's contract.

## Implementation boundaries

Keep memory-specific work under existing `resource/memory/` directories. Put shared
query machinery under `resource/runtime/` within the relevant crates. Prefer a
standalone runtime crate under `source/verus-meter/runtime/`, with final naming and
packaging established in task 1. Keep upstream syntax, attribute, driver, and
workspace hooks thin. Do not introduce a runtime dependency on VIR, rustc, or Z3.

Validate extraction, interpretation, and generated interfaces with ordinary Rust
tests and compiled integration examples. New formal proofs, equivalence lemmas,
verified arithmetic adapters, and verification of the integer library are outside
this work. Verus continues to verify the target function's existing resource
contract. Describe runtime queries as tested tooling for evaluating that contract;
do not claim the query implementation itself is formally verified.

Follow [AGENTS.md](../../../../AGENTS.md), the [build instructions](../../../../BUILD.md),
and the [memory model](../../model.md). Commit coherent, validated implementation
steps locally; do not push or publish without authorization. Mark tasks complete
only when their acceptance criteria hold. Keep raw logs disposable and preserve
lasting investigation evidence in commit messages and explanations beside code.
