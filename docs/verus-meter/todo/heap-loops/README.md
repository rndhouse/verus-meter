# Heap loop work

Work through these tasks in order. They extend precise peak-heap accounting and
the ownership information needed after loops and across function calls. They do
not promise support for every Rust program or every owning container.

1. [Compose iteration operations](01-compose-iteration-operations.md)
2. [Conditional ownership effects](02-conditional-ownership-effects.md)
3. [Transform children during traversal](03-transform-children.md)
4. [Indexed traversal and updates](04-indexed-traversal.md)
5. [Borrowed collections and incoming ownership](05-borrowed-and-incoming-ownership.md)
6. [General iteration counts and carried state](06-iteration-counts-and-state.md)
7. [Other loop forms and early exits](07-loop-forms-and-exits.md)

## Starting point

Local peak proofs and ownership summaries share checked loop records. Existing
collection summaries compose one unconditional append or pop per disjoint
persistent collection, including whole-child transfers, uniform construction,
and consumption. Collections can occupy fixed fields; children can contain
nested supported ownership shapes. Local peak proofs support some cases that
cannot yet be exported as precise ownership summaries.

## Rules for every task

- Build general ownership operations over supported layouts, not rules for
  individual combinations of `Vec`, `Box`, or user-defined fields.
- Keep local charges, complete physical ownership, and original-input allocation
  lifetimes distinct. Preserve child identity, order, and reservation facts.
- Derive effects from checked operations. Prove generated invariants at entry and
  on back edges; a summary is not permission to assume a memory bound.
- Reject transformations that cannot be represented. Do not replace missing
  ownership information with conservative aggregate accounting. Ordinary proved
  byte upper bounds remain part of the resource model.
- Keep peak allocation overlap separate from retained storage after an operation.
- Use each task's acceptance criteria to bound the implementation. Record any
  remaining restriction explicitly rather than claiming universal loop support.

## Validation and completion

Add regressions for distinct behavior and integration boundaries, including
caller-visible ownership after the loop, zero iterations, and insufficient
budgets. Preserve explicit rejection tests for unsupported transformations even
when their budgets are generous. Avoid a test matrix of every nesting spelling.

Follow [AGENTS.md](../../../../AGENTS.md) and the
[integration guide](../../integration.md) for checks and commits. Update the
[memory model](../../model.md) as behavior changes. Mark task checkboxes complete
only after implementation and relevant verification; keep investigation logs in
Git history rather than these task documents.
