# Heap loop work

Work through these tasks in order. They extend precise peak-heap accounting and
the ownership information needed after loops and across function calls. They do
not promise support for every Rust program or every owning container.

1. [Compose iteration operations](complete/01-compose-iteration-operations.md) — complete
2. [Conditional ownership effects](complete/02-conditional-ownership-effects.md) — complete
3. [Transform children during traversal](complete/03-transform-children.md) — complete
4. [Indexed traversal and updates](complete/04-indexed-traversal.md) — complete
5. [Borrowed collections and incoming ownership](complete/05-borrowed-and-incoming-ownership.md) — complete
6. [General iteration counts and carried state](complete/06-iteration-counts-and-state.md) — complete
7. [Other loop forms and early exits](07-loop-forms-and-exits.md)

## Starting point

Local peak proofs and ownership summaries share checked loop records and ordered
ownership effects. Multiple unconditional appends, removals, and whole-child
transfers compose on disjoint persistent roles, including through precise helper
programs and nested counted loops. Guarded effects also support stable scalar
conditions and counter thresholds with ordered, exact selection ranges. Roles
can occupy fixed fields; children can contain nested supported ownership shapes.
Parametric child transformations preserve nested extraction, replacement, growth,
release, and nonuniform generated footprints. Leaf-only results retain inferred
child descriptors. Ordered recurrences extend this to indexed updates, revisits,
and removal reindexing. Owned and borrowed incoming collections compose through
helper delegation with separate original lifetimes and local charges.

Shared progress supports literal integer strides, countdowns, moving scalar
bounds, checked collection lengths, and carried scalar exits. Symbolic allocation
bounds and nested counts compose with the same ownership effects. Stationary
updates can use complete forest induction beyond the finite proof window.
Other loop forms and exits remain in task 7. Local peak proofs support some cases
that cannot yet be exported as precise ownership summaries.

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
When a task is complete, move its numbered document into `complete/` and update
all links to it, including relative references inside the moved document.
