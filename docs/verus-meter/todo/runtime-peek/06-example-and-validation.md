# 6. User example and integration validation

## Goal

Ship one small executable example that lets a new user understand and run the
complete query-and-admit workflow, with a documented supported boundary.

## Work

- [ ] Add one focused example under `examples/resource/memory/`, selecting an
  existing supported allocation pattern with a simple input-dependent allowance.
  Verify the actual function body against that allowance; avoid an empty body
  used only to demonstrate macro expansion.
- [ ] Show `#[queryable_peak_memory]`, the single authoritative resource clause,
  the generated typed query, a comparison with an explicit configurable model-byte
  budget, and execution only when the bound fits. Establish the target function's
  preconditions separately and make that visible without distracting complexity.
- [ ] Let users run both admission and rejection paths. A rejection message must
  say that the declared allowance exceeds the budget, not that execution is
  mathematically impossible. Handle query errors distinctly if the final API is
  fallible. Do not hard-code a second copy of the budget formula in the caller.
- [ ] Add short build/run instructions with actual commands validated against the
  prepared environment. Link the example from the memory examples README and
  document its inputs, purpose, and constraints.
- [ ] Explain that the budget uses the existing abstract memory model, that query
  costs are separate, and that OS RAM discovery/reservation are future work. Keep
  comments focused on the user workflow rather than compiler implementation.
- [ ] Update the memory model documentation with the runtime-query API, supported
  expressions, precondition distinction, and formal/trust boundary.
- [ ] Integrate compiled example checks into existing Rust orchestration. Do not
  add Bash test scripts. Exercise both paths and ensure the successful path really
  calls the target function.

## Validation

Follow the current [project instructions](../../../../AGENTS.md), including the
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

- [Example index](../../../../examples/resource/memory/README.md)
- [Existing input-dependent allocation example](../../../../examples/resource/memory/heap/loops/buffer_collection.rs)
- [Example test harness](../../../../source/rust_verify_test/tests/examples.rs)
- [Build instructions](../../../../BUILD.md)
