# Third experiment: composing storage contracts across calls

Milestone introducing **lexical-slots-v2-64**. See [model.md](model.md) for the
authoritative current rules, implementation map, and run commands. This page
records the experiment and its validation.

The experiment added direct calls between resource-checked functions in the
same crate, plus array-to-slice coercions. The
[complete example](../../examples/resource/memory/resource_calls.rs) verifies `main` calling an
array-owning function, which then invokes insertion sort. Both the caller and
`main` have a 116-model-byte contract.

## Decisions carried forward

Callers use a callee's declared bound, keeping their proof independent of body
changes within that contract. Argument evaluation retains earlier results;
argument results overlap callee parameter slots at handoff. Parameters are
included in the callee bound and are not added to it again during execution.
The exact formula is in the [call rule](model.md#direct-calls).

All local annotated bodies are checked before accepting the crate. Executable
call cycles are rejected, including zero-cost self-recursion and mutual recursion,
so summaries cannot justify themselves circularly. Functional preconditions and
postconditions remain ordinary Verus obligations.

Array-to-slice coercions receive compiler provenance, while explicit helper calls
remain subject to normal call rules. Shared coercion adapters and implicit mutable
reborrows required dedicated accounting. Temporary backing arrays remain rejected.
Cross-crate summaries, generic/dynamic calls, value returns, and recursion were
left for later model decisions.

## Why the example costs 116

The eight-element array costs 32 bytes and remains live throughout the call.
Its literal initializer peaks at `32 + 32 + 4 = 68`. Creating and passing its
mutable slice descriptor stays below the final peak. Executing insertion sort
requires at most `32 + 84 = 116`. `main` has no additional live slots and inherits
the same bound through its call. Reducing the bound to 115 fails verification.

## Validation

Validated locally on 2026-11-06:

- Release workspace build, installed verifier build, and explicit vstd rebuild
  passed; vstd reported 2,226 verified and zero errors.
- All 93 resource tests passed: 36 original tests, 29 slice/arithmetic tests, and
  28 call-composition tests. The latter cover exact and insufficient budgets,
  argument overlap, declared-bound use, sequential/transitive calls, invalid
  callee contracts, functional proof failures, coercions, reborrows, borrowed
  temporary rejection, recursion, and storage-total overflow.
- The selected existing suites (`basic`, `functions`, `loops`, `size_of`,
  `mut_refs_slices_arrays`, `arrays`, `erase`, and `modes`) passed 373 tests, with
  five upstream-ignored tests. The complete upstream suite was not run.
- The complete example reported seven verified checks and zero errors, compiled
  with `--compile`, and ran successfully. Its trace reported peaks of 84, 116,
  and 116 for the sorter, array-owning caller, and `main` respectively.
- Workspace formatting and `git diff --check` passed.
