# 5. Formal correspondence and regression boundaries

## Goal

Complete the formal chain from the authoritative resource bound to runtime
evaluation, with the agreed trust assumptions and focused integration evidence.

For a function `f`, let `B(x)` denote its declared mathematical allowance and
`P(x)` its verification preconditions. Resource verification establishes the
modeled peak bound under `P(x)`. The query must return `B(x)` when it succeeds
within its specified domain. Together with `P(x)` and `B(x) <= budget`, this
supports admission under the existing memory model.

## Work

- [ ] Establish extraction correspondence between the retained expression and the
  original contract, including input conversion, sizes, helper substitution, and
  conditional selection. Validate any generated proof obligations with Verus;
  do not assume an equivalence merely because the generator emitted it.
- [ ] Establish evaluator correctness against mathematical expression semantics.
  State the exact assumptions about arbitrary-precision operations and any other
  trusted adapter in both code and documentation. Do not mark whole translated
  functions trusted as a shortcut around the intended correspondence proof.
- [ ] Separate successful-result exactness from successful evaluation for every
  supported input in the declared query domain. Include termination and
  representation invariants; make resource-limit qualifications explicit.
- [ ] Ensure budget comparison preserves the mathematical ordering, including
  values too large for a native integer. Keep existing function-bound `u64`
  checks and preconditions intact.
- [ ] Add negative regressions for incorrect expression/argument mapping where
  practical, unsupported nested helpers, missing contracts, and insufficient
  source memory allowances. A successful query must not mask failed resource
  verification of the target function.
- [ ] Cover the boundary between query evaluability and execution preconditions.
  Cover zero inputs, budget equality, branch selection, mathematical intermediates
  larger than native integers, and formula changes reaching compiled output.
- [ ] Check unannotated memory contracts and relevant upstream macro/erasure
  regressions to ensure opt-in extraction has not restricted existing programs.

## Acceptance

The implementation has a reviewed, explicit formal claim and no undisclosed
trusted translation fallback. Focused tests confirm integration and diagnostics;
they supplement the proof rather than replace it. If the agreed proof cannot be
completed, report the remaining gap and do not present the feature as complete.

## Starting points

- [Resource tests](../../../../source/rust_verify_test/tests/resource/)
- [Executable-spec verification tests](../../../../source/rust_verify_test/tests/exec_spec_verified.rs)
- [Memory semantics](../../model.md)
- [Required project checks](../../../../AGENTS.md)
