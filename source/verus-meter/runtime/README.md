# Runtime memory-query prototype

The macro retains constants, one unsigned parameter (`u8`, `u16`, `u32`, `u64`, or
`usize`), addition, multiplication, and parentheses as expression data. A generated
module shares the function's name and visibility. Its `peak_memory_bound` function
accepts the original parameter type and returns `Result<u64, Overflow>`.
Evaluation uses checked arithmetic; task 2 replaces this temporary numeric range
with arbitrary precision. Model-size queries, spec helpers, methods, and generic
functions are not supported yet. Attribute expansion must occur inside `verus!`.

The original function receives normal Verus resource verification. The generated
query module is external Rust tooling: its evaluator and connection to the source
contract are tested, not formally verified. Querying does not establish execution
preconditions or reserve RAM. Each macro pass emits data from the parsed resource
clause before ordinary signature erasure, with no generated files shared between
compiler passes. Keep typed resolution for additional expressions in the focused
resource modules when extending this path.

After preparing Verus as described in the repository's BUILD.md, run from `source/`:

```sh
cargo build --release -p verus_builtin_macros -p verus_meter_runtime
./target-verus/release/verus ../examples/resource/memory/contracts/runtime_query.rs --compile --extern verus_meter_runtime=target-verus/release/libverus_meter_runtime.rlib -o target-verus/runtime-query
./target-verus/runtime-query 1200
./target-verus/runtime-query 1000
```

The example queries `allocate(100)` and prints admission with allowance 1124 or
rejection when that allowance exceeds the supplied model-byte budget. The admitted
path allocates a vector and reports its capacity. The budget is an explicit input;
OS memory discovery and physical-memory correspondence remain separate work.
An optional second argument changes the buffer count at runtime (default 100).

Run unit tests and the compiled integration test from `source/`:

```sh
cargo test --release -p verus_meter_runtime
VERUS_QUERY_TEST_VERIFIER="$PWD/target-verus/release/verus" cargo test --release -p verus_meter_runtime --test query -- --ignored
```

The integration test is explicit because it requires prepared verifier artifacts
and the preceding runtime build. When using a separately staged distribution,
`VERUS_QUERY_TEST_DEPS` can supply its dependency search directory. The verifier
distribution must contain this branch's macro library; the example uses the direct
macro path so a prepared vstd's re-export cannot select an older macro version.
