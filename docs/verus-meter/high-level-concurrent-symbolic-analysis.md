# Concurrent symbolic memory analysis: high-level explanation

This is a plain-language companion to the
[technical assessment](concurrent-symbolic-analysis.md). It follows the same main
topics, explains the proposed design, and leaves source references and compiler
details to that report. This is a proposal; concurrent memory verification has
not been implemented by these documents.

## Assessment

The approach is practical for a useful subset of concurrent Rust. The main
question the verifier must answer is:

**Which allocations can be alive at the same time?**

Suppose four workers each need a 4 MiB temporary buffer. If they can all keep their
buffers alive together, the temporary storage can reach 16 MiB. If a verified
mutex protocol ensures that each buffer is allocated after locking and freed
before unlocking, only one buffer can be alive at a time. The temporary storage
then needs at most 4 MiB.

That saving should be part of the design from the beginning. Reducing each worker
to one number, such as “peak: 4 MiB,” loses the information needed to explain why
those peaks cannot overlap.

The recommendation is to keep information about **when memory is live and what
synchronization protects that lifetime**, then combine workers using those facts.

## Existing implementation and reusable foundations

Verus Meter already does much of the necessary work within a single execution:

- It derives memory costs from supported executable operations.
- It tracks when storage starts and stops contributing to memory use.
- It follows ownership moves without treating a move as a new allocation.
- It accounts for caller storage that remains alive during a helper call.
- It checks formulas that depend on inputs, such as a buffer length.
- It turns memory claims into proof obligations for Verus to check.

For example, two temporary buffers used one after another can reuse the same
allowance. If the first remains alive while the second is created, both count.
Concurrency extends this same lifetime question across threads.

The existing analysis also records summaries of functions: what they allocate,
what they retain, and how ownership changes. These summaries are valuable because
a caller can use a checked summary instead of analyzing the helper's entire body
again. That is what **compositional verification** means here.

The missing pieces include concurrent worker lifetimes, shared ownership and the
connection between synchronization and memory. Existing sequential memory tests
do not establish those properties.

The guarantee remains the [source-level memory model](model.md). It counts
modeled storage in bytes, not exact physical RAM use. OS thread stacks, allocator
overhead and fragmentation do not automatically become covered by this extension.

## What Verus concurrency already supplies

Verus already has tools for proving properties of concurrent code, including
thread creation/joining, atomics, shared invariants and a verified reader-writer
lock.

An **invariant** is a property that holds initially and remains true as the
program runs. For example, a lock protocol can maintain the invariant “at most
one worker holds this lock exclusively.”

That is useful, but it does not yet prove a memory bound. A worker could release
the lock while keeping its buffer. Another worker could then acquire the lock
and allocate another buffer. The lock still works correctly, but both buffers
are alive.

The extension therefore needs to connect two proofs:

1. The synchronization protocol limits who can hold the lock.
2. Every relevant buffer stays within its owner's lock-holding interval.

Verus supplies foundations for the first proof. Verus Meter must connect the
second proof to executable allocation and release operations.

## Proposed semantic foundation

Start with a small number of worker phases. For the mutex example:

| Worker phase | Temporary buffer alive? | Lock held? |
| --- | --- | --- |
| Waiting to acquire the lock | No | No |
| Acquired the lock, before allocation | No | Yes |
| Working with the buffer | Yes | Yes |
| Freed the buffer, before unlocking | No | Yes |
| Finished | No | No |

The verifier establishes that the program follows these lifetime rules, and that
only one worker can occupy a lock-held phase at once. It can then conclude that
only one worker can occupy the buffer-live phase.

The technical report calls this a **protocol-indexed simultaneous footprint**.
Here, “footprint” means the storage alive together, and “protocol-indexed” means
that the footprint is associated with a synchronization phase.

The proof does not need to try every possible thread schedule. It proves that
the rules hold initially and that every permitted step preserves them. The rules
then hold regardless of which worker runs next, including when workers pause or
wait for a long time.

Developers supply synchronization invariants and, when needed, mathematical
lemmas. The compiler supplies the memory facts from the code. A developer should
not have to manually increment a ghost counter whenever the program allocates;
forgetting such an increment must never make an incorrect bound pass.

## Precision and composition

### Thread counts and overlapping calls

Let `n` be the number of workers and `b` their individual temporary-buffer size.
The temporary-storage bounds are:

| Verified lifetime constraint | Upper bound on temporary storage |
| --- | --- |
| All workers may hold buffers together | `n * b` |
| One shared mutex covers every buffer's full lifetime | `b` when `n > 0`; otherwise zero |
| At most `k` workers hold permits covering their buffers' full lifetimes | `min(n, k) * b` |

A bound is **symbolic** when it uses parameters such as `n`, `b` and `k`, rather
than only fixed numbers. One proof can then cover every permitted input value.

These are bounds on the temporary buffers. The total bound must also cover
shared objects, worker-local storage, handles, results and other modeled storage.
Four workers waiting for a mutex still have storage of their own. Reducing the
buffer contribution from 16 MiB to 4 MiB does not make the whole program's bound
4 MiB.

Helper calls must preserve this detail. A summary saying “this helper needs a
buffer while this lock is held and frees it before returning” supports a tighter
proof than a summary saying only “this helper needs at most 4 MiB.”

### Spawn, completion, and join

A spawned worker continues running after the spawning call returns. Its storage
must therefore remain in the calculation.

A worker that has finished may also leave a result waiting to be collected.
Finishing execution does not necessarily free that result. Joining transfers the
result to the caller; it does not create a second copy of the same allocation.

For dynamic spawning, the useful quantity is often how many workers are alive
at once. A program might process a million jobs with four workers and bounded
storage. But if it keeps every job's output, that retained storage still grows.

The first implementation should require all workers to be joined within the
verified operation. Workers that outlive it need a more extensive model.

### Shared ownership and transfer

Count a shared allocation once, even if many workers hold references to it.
Count the individual reference handles separately where the model requires it.

Similarly, sending a buffer through a channel transfers ownership. The buffer
still exists while queued or held by the receiver. Moving it must neither remove
its memory cost nor count a second allocation.

Memory can be reused in the bound only once the previous storage has actually
been released under the model. Unlocking, finishing a task, or removing an item
from a logical collection does not by itself establish that release.

### Practical tightness

Precise bounds are realistic when programs have understandable phases and clear
rules about how many workers can enter each phase. Mutexes, bounded parallel work
and selected pipelines are good starting points.

The verifier will sometimes need stronger invariants from the developer. For
example, a loose description might allow two memory-heavy phases to overlap even
though the real program prevents that. Proving the missing relationship can
improve the bound.

Finding the smallest possible bound for arbitrary programs is not a realistic
general goal. The design should support tight proofs where the program's
structure permits them, while making any remaining overestimation clear.

## Synchronization mechanisms

Different mechanisms constrain different things:

| Mechanism | What matters for memory |
| --- | --- |
| Mutex | Buffers must be freed before releasing the same shared lock. Different locks do not exclude each other. |
| Semaphore | A permit must cover the entire buffer lifetime. Releasing it early allows another buffer to overlap. |
| Reader-writer lock | Exclusive writers can exclude each other. Multiple readers can still allocate simultaneously. |
| Atomics | An atomic operation must establish a verified protocol rule. Using an atomic variable alone does not limit allocations. |
| Channel | Account for queued buffers, buffers waiting to be sent, and buffers already received but still retained. |
| Barrier | A later phase can reuse an earlier phase's allowance only if the earlier storage is gone before the later allocations begin. |

More complex mechanisms need additional work. For example, lock-free structures
can keep removed nodes alive until it is safe to reclaim them. Those nodes still
consume storage even though they are no longer logically in the structure.

## Architecture and soundness obligations

The extension needs four connected capabilities:

1. **Recognize concurrent events.** Understand when workers start, locks are
   acquired, buffers move, workers finish and results are collected.
2. **Track memory through those events.** Keep every live allocation accounted
   for, including shared data and pending results.
3. **Use checked synchronization rules.** Connect actual lock or atomic operations
   to facts about which worker phases can coexist.
4. **Check the final formula.** Prove that the storage allowed by those rules fits
   the declared symbolic bound.

A proof is **sound** if a successful verification really establishes the claimed
bound under the stated model and assumptions. The most important requirement is
that no live storage can disappear from the calculation merely because a proof
annotation says a phase has ended.

For example, releasing a lock while retaining a buffer must either fail the
claimed lifetime rule or move the buffer into a separately counted retained-data
category. It cannot silently erase the buffer's cost.

The implementation must also understand the actual library operations it accepts.
A function named `lock` is not enough to establish mutual exclusion. Unsupported
operations must be rejected rather than assigned zero cost.

Initially, panic/unwinding, custom destructors, detached threads and complex
reclamation should have explicit restrictions. Their storage effects cannot be
ignored. The technical report describes the necessary trust and execution
boundaries in more detail.

## Proposed proof of concept and acceptance criteria

Use `n` workers, each allocating one temporary byte buffer of size `b`. For the
synchronized version, every worker follows this order:

```text
acquire the shared lock
allocate the buffer
use the buffer
free the buffer
release the lock
```

This is an illustrative sequence, not new Verus syntax. The technical report
includes a Rust sketch. The future demonstration must analyze its executable
allocations, not just prove a separate mathematical model of this sequence.

Let `H(n, b)` be a checked upper bound for all other modeled storage. Then compare:

```text
Unconstrained workers: total peak <= H(n, b) + n * b
Mutex-protected lifetimes, n > 0: total peak <= H(n, b) + b
```

`H` must come from checked accounting too. It cannot hide unexplained costs.
For zero workers, the temporary-buffer contribution is zero.

The demonstration should include deliberate mistakes:

| Change | Expected result |
| --- | --- |
| Claim less than `b` for one live buffer of size `b > 0` | Verification fails. |
| Remove the lock but keep the `b` claim for multiple workers | Verification fails because buffers can overlap. |
| Allocate before locking | The tight bound fails because waiting workers can retain buffers. |
| Unlock before freeing | The tight bound fails because the next worker can allocate while the old buffer remains alive. |
| Give every worker its own lock | The common-buffer bound fails because those locks do not exclude each other. |
| Allocate two buffers together under the lock | The one-buffer claim fails even though only one worker holds the lock. |

These failures are essential evidence that memory accounting follows the code.
They must not depend on someone remembering to update a separate ghost counter.
A loose total bound can contain spare room, so negative tests should target a
known necessary amount of storage, rather than simply subtract one byte from an
arbitrary allowance.

## Phased implementation plan

1. **Define the rules.** Specify worker lifetimes, shared storage, synchronization
   and which execution paths the initial model covers.
2. **Build the mutex demonstration.** Support a restricted set of workers and
   buffers. Prove both `n * b` and the tighter `b` contribution, and reject the
   incorrect lifetime variants. Tight synchronization-aware bounds belong here,
   in the first working version.
3. **Preserve precision across helpers.** Handle buffers created, passed, returned
   or freed inside functions without losing their lock and lifetime relationships.
4. **Support bounded parallel phases.** Add semaphore-style limits, unequal worker
   sizes and selected barrier patterns.
5. **Expand ownership and worker lifetimes.** Add richer shared ownership, returned
   buffers, bounded channels and dynamic worker pools.
6. **Address harder execution models.** Extend to broader library interfaces and,
   later, features such as detached work, cancellation and complex reclamation.

Each stage should retain the existing sequential guarantees and add tests for
both correct bounds and plausible mistakes.

## Alternatives and final recommendation

Adding independent worker peaks remains a useful conservative calculation when
nothing prevents their overlap. It should be one result the richer analysis can
produce, rather than the only information the architecture preserves.

Memory credits could be useful for programs that deliberately implement a fixed
pool or admission limit. They are not necessary to prove that mutex-protected
buffer lifetimes cannot overlap. Existing lock ownership proofs can provide the
synchronization evidence without making bytes into a resource developers must
manually distribute.

The recommended extension keeps the current symbolic analysis and teaches it to
combine **allocation lifetimes with verified synchronization rules**. Its first
working demonstration should prove the 4 MiB temporary-storage bound for four
workers and reject code changes that make those buffers overlap.
