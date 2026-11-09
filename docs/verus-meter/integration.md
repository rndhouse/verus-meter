# Maintaining the fork

Memory checking depends on the shape and ordering of Verus's intermediate code.
A clean Git merge still needs verification of these boundaries.

| Boundary | Fork code and upstream hooks |
| --- | --- |
| Syntax | [syn](../../dependencies/syn/src/verus.rs) defines memory clauses, formulas, sections, and checkpoints; [prettyplease](../../dependencies/prettyplease/src/expr.rs) prints them. |
| Macros | [resource/memory](../../source/builtin_macros/src/resource/memory) extends the [syntax visitor](../../source/builtin_macros/src/syntax.rs). Its child-module declaration follows the quoting macros to preserve their scope and hygiene. |
| Rust translation | [Frontend memory support](../../source/rust_verify/src/resource/memory) translates budget markers and recognizes standard operations by compiler identity. Call lowering, headers, and function translation retain small hooks. |
| Verification pipeline | [query.rs](../../source/rust_verify/src/query.rs) collects execution modes and invokes [pipeline.rs](../../source/rust_verify/src/resource/memory/pipeline.rs). |
| Analysis | [VIR memory support](../../source/vir/src/resource/memory) checks accounting and produces ordinary proof obligations. Shared VIR types and visitors carry its metadata. |

Type-only `mem_size` queries in specifications are resolved before each
function's well-formedness and mode checks, using the shared model layouts.

Keep the memory pass **after all local bodies are mode-checked and before export,
resolution inference, or simplification**. Later transformations can obscure the
source places and lifetimes the model measures. Generated assertions need fresh
AST identities. Erase memory metadata only after analysis succeeds; keep the
assertions for normal Verus verification.

Macro lowering must preserve execution and ghost erasure. Resolve section budget
names before visiting its declarations, and retain binding scopes for checkpoints.
Compiler upgrades need a review of borrow/coercion lowering, move/copy provenance,
and the identities used for supported standard operations.

When resolving syntax conflicts, edit the AST definitions first, then run
`cargo run` in `dependencies/syn/codegen/` to regenerate the schema and derived files.
Keep historical model variants and their ordering in
[model.rs](../../source/vir/src/resource/memory/model.rs); a semantic change needs
a distinct model identity rather than reinterpreting an old contract.

After an upgrade, rebuild with `cargo make build` from `source/`, then run:

```sh
cargo test --release -p rust_verify_test --test resource memory:: -- --test-threads=2
cargo test --release -p rust_verify_test --test examples resource_ -- --test-threads=2
cargo test --release -p vir --lib resource::memory
```

Also run `test_resources` from `dependencies/syn/`, the prettyprinter tests, and
upstream regressions covering references, arrays, modes, erasure, and function
contracts. Passing memory tests alone does not establish upstream compatibility.
