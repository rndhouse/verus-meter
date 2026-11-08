# Verus Meter Project Instructions

Keep project instructions tracked in Git so clones and worktrees receive them.
Keep these instructions self-contained and use repository-relative references;
do not depend on machine-local guidance or configuration outside the repository.
Read applicable nested `AGENTS.md` files before editing their directories.

## Completing work

Commit completed, validated changes in coherent commits before reporting the task
finished, unless the user explicitly asks to leave them uncommitted. Review the
exact staged diff, preserve unrelated changes, and report the commit and checks.
If a change cannot be completed or committed, explain what remains and why.
Pushing or publishing requires user authorization beyond a local commit.

Keep commit messages focused on the change without agent attribution or agent
co-author trailers. Preserve meaningful validation results in commit messages
when useful; keep raw logs and build output in ignored disposable locations.

## Project layout and conventions

This is a Verus fork. Read `README.md`, `BUILD.md`, and
`docs/verus-meter/integration.md` for the memory model's integration boundaries.
The Cargo workspace is `source/`; run workspace commands there with the pinned
toolchain in `rust-toolchain.toml`.

Preserve upstream architecture, formatting, package publishing settings, and
existing lint policy. Apply the conventions below to new and substantively
changed first-party code without unrelated rewrites of inherited or vendored code.
Use the existing `source/rustfmt.toml` and `dependencies/syn/rustfmt.toml`.
Retain the upstream `verusfmt` workflow for Verus syntax as documented in
`CONTRIBUTING.md`.

## Implementation and documentation

Inspect existing changes before editing and preserve unrelated work. Keep
fork-specific behavior in focused modules and upstream integration points thin.
Prefer existing project facilities and established libraries over custom
reimplementations. Make durable fixes in source, not only in generated artifacts.

Use Rust for new first-party implementation and development tooling where the
integration permits it. Keep process and filesystem test orchestration in Rust;
do not add new Bash test scripts. Preserve established tooling boundaries.

Explain domain concepts, invariants, and non-obvious decisions beside the code.
Document public APIs and give struct fields meaningful comments, using doc
comments for public fields. Keep examples executable and document their purpose,
declarations, and meaningful constraints. Review unnecessary public visibility
and avoid blanket lint suppressions.

Use named formatting placeholders and readable multiline templates for embedded
scripts or configuration. Separate distinct declarations and conceptual blocks
with blank lines, while keeping tightly related statements together. Use the
existing formatter rather than introducing custom formatting checks.

Keep overview documentation short and focused on responsibilities and boundaries.
Update documentation when behavior changes. Keep implementation details in code
and lasting investigation evidence in Git history; avoid status-report collections.

## Focused memory checks

Choose checks for the affected behavior. For memory accounting changes, run from
`source/`:

```sh
cargo fmt -p vir -- --check
cargo test --release -p vir --lib resource::memory
cargo build --release -p rust_verify
cargo test --release -p rust_verify_test --test resource memory:: -- --test-threads=2
cargo test --release -p rust_verify_test --test examples resource_ -- --test-threads=2
```

Build the verifier before running integration tests so they exercise the changed
code. Follow `docs/verus-meter/integration.md` for broader checks when modifying
syntax, macros, frontend integration, or upgrading upstream.

For Rust code, dependencies, or build tooling changes, run appropriate tests,
formatting checks, and Clippy for the affected packages and targets. For public API
or documentation-lint changes, also run strict rustdoc with relevant features.
Use the prepared environment and pinned tools; do not provision tools implicitly.

Focus regression tests on distinct behavior and integration boundaries rather than
mirroring implementation or configuration literals. Run relevant checks once the
change is ready; repeat or broaden them when changes, failures, or unresolved
concerns justify it. Report actual results and material verification gaps.

For instruction or prose edits, check whitespace with `git diff --check` and verify
references; do not rebuild. For Rust spacing-only edits, also check formatting.
Verify changed documentation code examples with focused doctests or example checks.
