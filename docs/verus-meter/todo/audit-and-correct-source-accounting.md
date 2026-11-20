# Audit and correct source memory accounting

Bring the verifier into line with the [source accounting policy](../accounting/README.md). Remove charges for implementation details while preserving every source-visible allocation and overlap. This audit covers sequential accounting. Concurrent proof work has its [own tracker](concurrent/README.md).

## What needs checking?

- [ ] Inventory the operations the verifier accepts, starting from frontend intrinsics and executable expression handling. Cover inline values and temporaries, borrowing and copying, owning containers, iteration, and calls. Group operations only when their storage effects agree.
- [ ] For each family, identify the source event that creates a charge, its size, who keeps it live, and what transfers or releases it. Distinguish the documented effect of a library operation from executable user code run during that operation.
- [ ] Compare the rule with direct execution, helper and loop summaries, regressions, runnable examples, and user-facing docs. Check the same ownership effect across a helper boundary and a section boundary.
- [ ] For missing operation support or ownership information, check the diagnostic with a generous budget. A missing rule must never silently grant zero cost.
- [ ] Record each discrepancy with a reproducer, the expected charge, and its resolution. Update the accounting page when a policy decision changes. Keep validation evidence with the fix in Git.

## First corrections and controls

- [ ] **Borrowed iteration.** Remove charges for implicit iterator state and the reference used only to visit an item. Show that storing the item still costs a slot and consuming iteration still retains the input backing and unvisited payloads.
- [ ] **Streaming versus staging.** Verify the single checksum loop for a variable input length with one result slot per input plus the checksum allowance. Under the identical bound, show a budget violation for the split loop that retains a second collection. Check the reason for failure and isolate loop-length inference if the streaming proof still fails.
- [ ] **Consuming conversion versus explicit replacement.** The boxed-slice conversion currently checks overlap with a possible internal replacement. Remove that charge. Keep a negative test where user code, directly or in a helper, creates a second buffer while the original is live. [Conversion implementation](../../../source/vir/src/resource/memory/boxed_slices.rs)
- [ ] **Reservation versus private growth.** Use the committed vector rule in `fc76adae3` as a control. Exercise pushes below and beyond a reservation, removal back to the reservation, and growth through a borrowed helper. [Vector rules](../accounting/which-bytes-count/collections/vectors.md)
- [ ] **Move versus duplication.** Moving an owning buffer must fit with one backing. Creating an independent copy while the first is live must require both. For clone operations, check the specific operation's ownership semantics and support status.

## When is the audit complete?

- [ ] Every supported family has a documented rule and checked implementation. Every discrepancy has a resolution and a regression. Distinguish committed fixes from pending edits.
- [ ] For each correction, independently derive the expected bytes and check a fitting case and a budget violation. Include a one-byte-short check where the peak is known exactly. An unsupported-operation or solver diagnostic cannot stand in for a budget violation.
- [ ] Verify affected examples and run the repository's focused memory checks against the rebuilt verifier. Preserve earlier results against the revision they tested. The previous correctness and test reviews remain available in Git at `fc76adae3`.
