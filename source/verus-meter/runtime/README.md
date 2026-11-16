# Runtime memory-query prototype

The macro retains constants, unsigned parameters (`u8`, `u16`, `u32`, `u64`, or
`usize`), Boolean parameters, addition, multiplication, comparisons, Boolean
operators, and conditionals as expression data. A generated
module shares the function's name and visibility. Its `peak_memory_bound` function
accepts the original parameter types and returns `Result<ModelBytes, QueryError>`.
Evaluation uses the workspace's arbitrary-precision integer library. `ModelBytes`
supports `fits_within(budget: u64)`, decimal display, ordering against another
allowance, and explicit `to_u64()` conversion returning `NativeRangeError` when
the result is too large. Third-party numeric types stay private. Attribute
expansion must occur inside `verus!`.

The query module has the function's name and visibility; its callable method is
`peak_memory_bound` with the original argument order and types. Existing types or
modules with that name must be renamed to leave the query namespace available.
Rust checks imported names and conditional namespace conflicts. Function-level
`cfg` conditions, configuration inside `cfg_attr`, and test-only removal also
apply to the query module. Put the query attribute directly on the function;
conditional query markers inside `cfg_attr` are rejected. Methods, traits, and
other non-function items receive explicit diagnostics.

Local nongeneric spec helpers in the same `verus!` item scope can supply the
formula. Supported bodies contain immutable scalar lets, nested supported helper
calls, and a final scalar expression. Local shadowing and nonnegative casts to
mathematical `nat`/`int` preserve their values. All reachable bodies and branches
are inspected, including unused initializers. Recursion, higher-order application,
native casts, other arithmetic operations, executable or external helper bodies,
and helpers outside that item scope are rejected. Source parameters retain their
order and Rust types, including unused parameters.
Helper and peak targets controlled by configuration attributes are rejected to
avoid selecting an incorrect declaration before Rust evaluates the conditions;
use an unconditional helper containing a supported conditional expression.

`peak(helper(arguments))` expands the local checked function's declared allowance
with the same argument substitution. Cycles and missing contracts are errors.
Argument-free `peak(helper)` remains unsupported by runtime queries; its existing
verification semantics are unchanged.

`value_size` supports native integer and Boolean types, unit, fixed integer
arrays, and the standard `Vec`, `Box`, and supported `Option` handles. `ref_size`
supports references to sized values and slices. Rust resolves aliases and type
identity through hidden size traits; no ABI `size_of` is used. Primitive widths,
array arithmetic, and reference widths come from `verus_meter_model`, shared with
the existing verifier layouts. Custom structs and other types have no runtime
size implementation and produce trait diagnostics. Existing resource checks
still validate layouts and supported contents. Methods and generic query
functions remain outside this version. Size queries on computed helper locals
need an explicit source type annotation when their type is not retained from an
input or helper declaration.

The original function receives normal Verus resource verification. The generated
query module is external Rust tooling: its evaluator and connection to the source
contract are tested, not formally verified. Querying does not establish execution
preconditions or reserve RAM. Each macro pass emits data from the parsed resource
clause before ordinary signature erasure, with no generated files shared between
compiler passes. Keep typed resolution for additional expressions in the focused
resource modules when extending this path.
Queries can evaluate well-typed inputs outside the function's preconditions, but
that result does not establish that execution is valid. Existing verification
bypass flags such as `--no-verify` retain their behavior; the attribute does not
enforce verification or make an unchecked build verified.

The runtime has separate integer and Boolean expression types, indexed scalar
inputs, comparisons, lazy logical operators, and conditional integer expressions.
Their constructors are hidden implementation interfaces for generated code, with
private nodes. Negative final byte values and missing or
incorrectly typed arguments produce `QueryError`. An allowance greater than `u64`
remains a valid result; a small evaluated allowance does not certify execution
preconditions. Source resource verification retains its existing `u64` obligations.

Evaluation uses stack space proportional to expression depth and storage
proportional to integer size. There is no custom evaluation-limit framework;
stack or allocator exhaustion is not reported as a recoverable query error.

## Run the example

The [runtime-query example](../../../examples/resource/memory/contracts/runtime_query.rs)
declares one input-dependent allowance on a function that reserves a byte buffer.
Its `allocation_memory` spec helper names the input, capacity argument, vector
handle, and backing-storage contributions, using `value_size` for their model sizes.
The caller checks that the count is positive, queries the allowance, and calls
the function only when it fits the supplied budget. No arithmetic formula is
repeated in the caller. Query errors terminate with `memory query failed`,
separately from a budget rejection.

Prepare a matching verifier, macro library, and vstd as described in
[BUILD.md](../../../BUILD.md), and set `VERUS_Z3_PATH` to the prepared solver.
Run from `source/`:

```sh
cargo run --release -p verus_meter_tools --bin prepare-resource-runtime -- target-verus/release
./target-verus/release/verus ../examples/resource/memory/contracts/runtime_query.rs --compile -o target-verus/runtime-query
./target-verus/runtime-query 150
./target-verus/runtime-query 100
./target-verus/runtime-query 300 200
```

The three runs print:

```text
Admitted: allowance 134, capacity 100
Declined: allowance 134 exceeds budget 100
Admitted: allowance 234, capacity 200
```

The first argument is a `u64` model-byte budget; the optional second argument is a
positive `u16` byte count (default 100). The precondition check is independent of
the allowance query: a successful query alone does not justify calling the target.
A rejection says the declared allowance exceeds the budget; it does not prove
execution cannot fit. The admitted path reserves a real vector and reports its
capacity. The allowance covers the target under the existing abstract model;
the caller and query have separate costs. OS RAM discovery, reservation, and
correspondence with physical memory remain future work.

## Build integration

The normal `cargo make build` and legacy default `vargo build` prepare the runtime
bundle automatically. The explicit preparation command above also works for an
existing in-tree build. Standalone Verus discovers `resource-runtime/` beside its
other artifacts and uses its isolated library dependencies. Release staging copies
the bundle. Older distributions without it remain usable for programs that do not
query bounds. Explicit runtime `--extern` arguments take precedence.

For Cargo projects, add an unrenamed `verus_meter_runtime` path dependency pointing
to this fork's `source/verus-meter/runtime`, alongside the project's vstd dependency,
and use `cargo verus build`. Cargo supplies that runtime and its dependency graph;
the standalone bundle is not injected into Cargo builds.

## Checks

Run unit tests and the compiled integration suite from `source/`:

```sh
cargo test --release -p verus_meter_runtime
VERUS_QUERY_TEST_VERIFIER="$PWD/target-verus/release/verus" cargo test --release -p verus_meter_runtime --test query -- --ignored --test-threads=1
```

The explicit integration suite requires this branch's matching verifier artifacts,
prepared runtime bundle, `cargo-verus`, `create-release`, and
`prepare-resource-runtime` binaries. Set `VERUS_Z3_PATH` to the prepared solver.
It checks the interface and compiled examples, a relocated release distribution,
runtime bundle refresh, and a Cargo client rebuilt after its formula changes.
Regression cases also check exact input conversion and arithmetic, helper
substitution and local size queries, queries outside preconditions, and resource
verification failures with and without the query attribute.
The ordinary resource-example suite also verifies this example, using standalone
artifact discovery for its runtime dependency.
