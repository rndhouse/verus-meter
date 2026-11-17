# 6. User example and integration validation

## Goal

Polish the example started in task 1 so a new user can understand and run the
complete query-and-admit workflow, then finish integration validation.

## Work

- [x] Finish the one focused example under `examples/resource/memory/`, using an
  existing supported allocation pattern with a simple input-dependent allowance.
  Verify the actual function body against that allowance; avoid an empty body
  used only to demonstrate macro expansion.
- [x] Show `#[queryable_peak_memory]`, the single authoritative resource clause,
  the generated typed query, a comparison with an explicit configurable model-byte
  budget, and execution only when the bound fits. Establish the target function's
  preconditions separately and make that visible without distracting complexity.
- [x] Let users run both admission and rejection paths. A rejection message must
  say that the declared allowance exceeds the budget, not that execution is
  mathematically impossible. Handle query errors distinctly if the final API is
  fallible. Do not hard-code a second copy of the budget formula in the caller.
- [x] Add short build/run instructions with actual commands validated against the
  prepared environment. Link the example from the memory examples README and
  document its inputs, purpose, and constraints.
- [x] Explain that the budget uses the existing abstract memory model, that query
  costs are separate, and that OS RAM discovery/reservation are future work. Keep
  comments focused on the user workflow rather than compiler implementation.
- [x] Update the memory model documentation with the runtime-query API, supported
  expressions, and precondition distinction. State that the target's resource
  contract is verified while the query implementation is tested Rust tooling.
- [x] Integrate compiled example checks into existing Rust orchestration. Do not
  add Bash test scripts. Exercise both paths and ensure the successful path really
  calls the target function.

## Validation

Follow the current [project instructions](../../../../../../AGENTS.md), including the
focused memory checks from `source/`:

```sh
cargo fmt -p vir -- --check
cargo test --release -p vir --lib resource::memory
cargo build --release -p rust_verify
cargo test --release -p rust_verify_test --test resource memory:: -- --test-threads=2
cargo test --release -p rust_verify_test --test examples resource_ -- --test-threads=2
```

Also run appropriate formatting, tests, Clippy, and strict rustdoc for the new
runtime API and changed packages/targets. Check affected macro/parser/prettyprinter
packages and relevant upstream regressions for references, arrays, modes, erasure,
iterators, and function contracts. Use prepared pinned tools; report missing tools
or checks rather than installing tools implicitly. Build the relevant verifier
and runtime artifacts before integration tests. Validate documentation examples
through the executable example checks and run `git diff --check`.

## Acceptance

A new user can follow the documented commands and observe both admission and
rejection, using the same bound checked by Verus. The final handoff reports actual
checks and any material gaps. Review exact staged diffs, preserve unrelated work,
and commit coherent validated changes; pushing or publishing requires separate
authorization. Mark tasks complete only after their criteria are met.

## Starting points

- [Example index](../../../../../../examples/resource/memory/README.md)
- [Existing input-dependent allocation example](../../../../../../examples/resource/memory/heap/loops/buffer_collection.rs)
- [Example test harness](../../../../../../source/rust_verify_test/tests/examples.rs)
- [Build instructions](../../../../../../BUILD.md)

## Implemented boundary

Implemented on `feature/queryable-peak-memory` in commit `4fb114354`, with runtime
bundle isolation in `8bfb9bc0b`. The example checks its positive-count precondition,
queries the single declared allowance, compares it with a configurable model-byte
budget, and reserves a real byte buffer only on admission. Query errors are distinct
from allowance-based rejection. Instructions show both paths and a changed count,
including their actual output.

The ordinary Rust example harness verifies the example through standalone artifact
discovery. Compiled checks exercise admission, equality, rejection, and invalid
inputs, and observe the allocated buffer's capacity. Runtime preparation uses a
private Cargo output directory so concurrent builds cannot replace its libraries
while the bundle is being collected.

Documentation distinguishes execution preconditions, model allowances, separate
query costs, and future OS RAM discovery or reservation. The target's resource
contract remains verified; runtime queries remain tested Rust tooling. Final
validation results and tooling limitations are recorded in the implementation
commits.
