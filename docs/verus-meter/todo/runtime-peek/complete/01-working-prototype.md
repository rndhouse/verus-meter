# 1. Working prototype

## Goal

Get one function's declared memory allowance into a callable runtime query and
use it to decide whether to execute the function. Resolve compilation questions
through this working example before expanding the design.

## Work

- [x] Inspect the macro, resource-lowering, and ghost-erasure stages to identify
  the smallest integration path. Reuse the existing parsed resource clause.
- [x] Support `#[queryable_peak_memory]` on a safe, nongeneric free function with
  one unsigned scalar parameter and a bound using constants, addition, and
  multiplication. Reject unsupported forms explicitly.
- [x] Retain the formula as expression data and generate a typed
  `foo::peak_memory_bound(...)` wrapper. Evaluate it with a small shared interpreter;
  keep the resource clause as the single source of the formula.
- [x] Take the retained expression through verification of the original function,
  ghost erasure, and executable compilation. Choose the bridge based on existing
  facilities and keep it tied to the current source and argument mapping.
- [x] Use only enough evaluator and result API to run the example. Checked native
  arithmetic is acceptable here for a bounded input type and formula; do not
  silently wrap. Task 2 develops this into the arbitrary-precision runtime.
- [x] Start one example under `examples/resource/memory/` with a real supported
  function body, its resource clause, a query, and an explicit configurable budget.
  Establish the function's preconditions and exercise admission and rejection.
- [x] Add a focused compiled check for the example and a check that changing the
  source allowance changes the query result. Check a missing resource clause and
  an incorrectly typed query argument produce useful failures.
- [x] Keep implementation under `resource/memory/`, `resource/runtime/`, and a
  runtime crate under `source/verus-meter/` as appropriate. Document the chosen
  compilation bridge beside the code and record actual run commands.

## Acceptance

The example compiles and runs both budget-decision paths. The original function
passes its existing resource verification, and the runtime query evaluates the
formula written in that contract. A focused test confirms the expected result.
There is no requirement to formally verify extraction, the evaluator, or their
equivalence. Record the prototype's supported scope and any temporary arithmetic
restriction so task 2 can extend it directly.

## Starting points

- [Architecture](../../../../../source/CODE.md)
- [Macro integration](../../../../../source/builtin_macros/src/syntax.rs)
- [Resource macros](../../../../../source/builtin_macros/src/resource/)
- [Compiler driver](../../../../../source/rust_verify/src/driver.rs)
- [Workspace and existing arithmetic dependency](../../../../../source/Cargo.toml)
- [Memory examples](../../../../../examples/resource/memory/README.md)

## Implemented boundary

Implemented on `feature/queryable-peak-memory` in commit `ddbdebf44`. The macro
retains constants, its single unsigned input, sums, products, and parentheses as
static expression data in both compilation passes. The shared interpreter uses
checked `u64` arithmetic and the wrapper returns `Result<u64, Overflow>`.

The runtime example accepts a model-byte budget and an optional buffer count.
Its target function receives ordinary resource verification; the query module
is external Rust tooling. Compiled integration coverage checks both decisions,
changed formulas, runtime inputs, and rejected query declarations/calls. Run
instructions live in `source/verus-meter/runtime/README.md` on the implementation
branch. Arbitrary precision remains task 2, and expanded expression support,
interface integration, and diagnostic coverage remain tasks 3 through 6.
