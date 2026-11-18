//! Identity links travel with ownership forests; their targets are charged once
//! by the enclosing accounting domain. These pure descriptors do not establish
//! that an executable handle exists or authorize its creation or destruction.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::blocks::generate_children;
#[cfg(verus_keep_ghost)]
use super::forest::{Record, prefix, subtree, without};
#[cfg(verus_keep_ghost)]
use super::ranges::{repeat, shift_children};

verus! {

broadcast use crate::seq::group_seq_axioms;

/// Typed identity queries for aliases and join handles. An identity can include
/// invocation, worker-family and loop-index binders; a family query groups
/// indices without changing their individual identities or multiplicity.
pub enum Reference {
    /// One strong alias. Several records may refer to the same canonical root.
    Shared(Seq<int>),
    /// A handle for one publication; transferring it does not complete the worker.
    Worker(Seq<int>),
    /// All handles with this family prefix and a nonempty occurrence suffix.
    /// Nested loops/calls can contribute several occurrence coordinates.
    /// This query cannot construct a handle or establish worker completion.
    WorkerFamily(Seq<int>),
}

/// A strong handle's owner node has no separate byte charge. Its inline slot
/// belongs to its containing value, and backing storage belongs to the root.
pub open spec fn shared_reference(path: Seq<int>, identity: Seq<int>) -> Record {
    Record { kind: -1, reference_identity: identity, ..super::forest::empty_record(path) }
}

/// Join-handle ownership names a worker independently of the source handle slot.
pub open spec fn worker_reference(path: Seq<int>, identity: Seq<int>) -> Record {
    Record { kind: -2, reference_identity: identity, ..super::forest::empty_record(path) }
}

/// A publication freezes its checked input and result descriptions. A result
/// description is a conditional ownership effect of the verified body; storing
/// it here neither executes that body nor charges its future allocations.
pub open spec fn worker_observation(
    path: Seq<int>,
    identity: Seq<int>,
    inputs: Seq<Record>,
    result: Seq<Record>,
) -> Record {
    Record {
        worker: |result_view: bool|
            if result_view {
                result
            } else {
                inputs
            },
        ..worker_reference(path, identity)
    }
}

/// Scalar observations have no byte charge or ownership multiplicity. Their
/// signed mathematical value is preserved even for a negative source integer.
pub open spec fn scalar_observation(path: Seq<int>, value: int) -> Record {
    Record { kind: -3, reference_identity: seq![value], ..super::forest::empty_record(path) }
}

/// Recover a scalar frozen by a checked closure construction.
pub open spec fn scalar_value(record: Record) -> int {
    record.reference_identity[0]
}

/// Capture observations follow the worker identity through ownership moves.
pub open spec fn worker_inputs(record: Record) -> Seq<Record> {
    (record.worker)(false)
}

/// The checked conditional result description, independent of the handle path.
pub open spec fn worker_result(record: Record) -> Seq<Record> {
    (record.worker)(true)
}

/// Classify an existing link by its publication identity independently of
/// proving that its conditional result is well formed.
pub open spec fn worker_in_family(record: Record, family: Seq<int>) -> bool {
    record.kind == -2 && family.len() == 2 && record.reference_identity.len() >= 2
        && record.reference_identity[0] == family[0] && record.reference_identity[1] == family[1]
}

/// This predicate describes an existing link; it cannot create an occurrence.
pub open spec fn worker_matches(record: Record, family: Seq<int>) -> bool {
    (if family.len() == 2 {
        worker_in_family(record, family)
    } else {
        record.kind == -2 && family.is_prefix_of(record.reference_identity)
    }) && super::forest::well_formed(worker_result(record))
}

/// Count matching publications in the occupied slots of a handle vector. A
/// popped handle is accounted for by its new owner outside this prefix.
#[verifier::opaque]
pub open spec fn worker_family_count(memory: Seq<Record>, length: int, family: Seq<int>) -> nat
    decreases length,
{
    if length <= 0 {
        0
    } else {
        worker_family_count(memory, length - 1, family) + if worker_in_family(
            super::forest::lookup(memory, seq![length - 1]),
            family,
        ) {
            1nat
        } else {
            0nat
        }
    }
}

/// A vector with no occupied slots contributes no workers.
pub broadcast proof fn worker_family_count_empty(memory: Seq<Record>, length: int, family: Seq<int>)
    requires
        length <= 0,
    ensures
        #[trigger] worker_family_count(memory, length, family) == 0,
{
    reveal(worker_family_count);
}

/// Two forests with identical records at each occupied slot
/// contribute the same count, regardless of their backing or other records.
proof fn worker_family_count_agrees(
    left: Seq<Record>,
    right: Seq<Record>,
    length: int,
    family: Seq<int>,
)
    requires
        forall|i: int|
            0 <= i < length ==> #[trigger] super::forest::lookup(left, seq![i])
                == super::forest::lookup(right, seq![i]),
    ensures
        worker_family_count(left, length, family) == worker_family_count(right, length, family),
    decreases length,
{
    reveal_with_fuel(worker_family_count, 2);
    if length > 0 {
        worker_family_count_agrees(left, right, length - 1, family);
    }
}

/// A join handle recovered by lookup came from an occupied ownership path.
proof fn worker_lookup_present(memory: Seq<Record>, path: Seq<int>)
    ensures
        super::forest::lookup(memory, path).kind == -2 ==> super::forest::contains(memory, path),
    decreases memory.len(),
{
    reveal_with_fuel(super::forest::lookup, 2);
    reveal_with_fuel(super::forest::contains, 2);
    if memory.len() > 0 {
        worker_lookup_present(memory.drop_last(), path);
    }
}

/// Appending a handle adds one to its publication family’s count.
pub broadcast proof fn worker_family_count_push(
    left: Seq<Record>,
    child: Seq<Record>,
    path: Seq<int>,
    length: int,
    family: Seq<int>,
)
    requires
        length > 0,
        path == seq![length - 1],
        super::forest::lookup(child, Seq::empty()).kind == -2,
    ensures
        #[trigger] worker_family_count(left + prefix(child, path), length, family)
            == worker_family_count(left, length - 1, family) + if worker_in_family(
            super::forest::lookup(child, Seq::empty()),
            family,
        ) {
            1int
        } else {
            0int
        },
{
    use super::selection::{lookup_add, contains_prefix, lookup_prefix};
    let next = left + prefix(child, path);
    assert forall|i: int| 0 <= i < length - 1 implies #[trigger] super::forest::lookup(
        next,
        seq![i],
    ) == super::forest::lookup(left, seq![i]) by {
        assert(!path.is_prefix_of(seq![i])) by {
            assert(path[0] != seq![i][0]);
        }
        lookup_add(left, prefix(child, path), seq![i]);
        contains_prefix(child, path, seq![i]);
    }
    worker_family_count_agrees(next, left, length - 1, family);
    worker_lookup_present(child, Seq::empty());
    lookup_add(left, prefix(child, path), path);
    contains_prefix(child, path, path);
    lookup_prefix(child, path, path);
    assert(path.skip(path.len() as int) =~= Seq::<int>::empty());
    reveal(worker_family_count);
}

/// Removing the last slot subtracts exactly the family of the extracted handle.
pub broadcast proof fn worker_family_count_pop(
    memory: Seq<Record>,
    path: Seq<int>,
    length: int,
    family: Seq<int>,
)
    requires
        length >= 0,
        path == seq![length],
    ensures
        #[trigger] worker_family_count(without(memory, path), length, family) + if worker_in_family(
            super::forest::lookup(subtree(memory, path), Seq::empty()),
            family,
        ) {
            1int
        } else {
            0int
        } == worker_family_count(memory, length + 1, family),
{
    let next = without(memory, path);
    assert forall|i: int| 0 <= i < length implies #[trigger] super::forest::lookup(next, seq![i])
        == super::forest::lookup(memory, seq![i]) by {
        assert(!path.is_prefix_of(seq![i])) by {
            assert(path[0] != seq![i][0]);
        }
        super::selection::lookup_without(memory, path, seq![i]);
    }
    worker_family_count_agrees(next, memory, length, family);
    super::selection::lookup_subtree(memory, path, Seq::empty());
    assert(path + Seq::empty() =~= path);
    reveal(worker_family_count);
}

/// Scope exit must not discard a handle hidden in a runtime ownership forest.
pub open spec fn workers_empty(memory: Seq<Record>) -> bool {
    forall|i: int| 0 <= i < memory.len() ==> #[trigger] memory[i].kind != -2
}

/// Query links without adding nested datatype invariants to every byte record.
pub open spec fn refers_to(record: Record, reference: Reference) -> bool {
    record.bytes == 0 && record.capacity == 0 && record.length == 0 && match reference {
        Reference::Shared(identity) => record.kind == -1 && record.reference_identity == identity,
        Reference::Worker(identity) => record.kind == -2 && record.reference_identity == identity,
        Reference::WorkerFamily(family) => record.kind == -2 && record.reference_identity.len()
            > family.len() && family.is_prefix_of(record.reference_identity),
    }
}

/// Multiplicity includes every alias. It does not assume path or identity
/// uniqueness, and never counts the referenced payload's bytes again.
#[verifier::opaque]
pub open spec fn reference_count(memory: Seq<Record>, reference: Reference) -> int
    decreases memory.len(),
{
    if memory.len() == 0 {
        0
    } else {
        reference_count(memory.drop_last(), reference) + if refers_to(memory.last(), reference) {
            1int
        } else {
            0int
        }
    }
}

/// Concatenation preserves both distinct identities and repeated aliases.
pub proof fn reference_count_add(left: Seq<Record>, right: Seq<Record>, reference: Reference)
    ensures
        reference_count(left + right, reference) == reference_count(left, reference)
            + reference_count(right, reference),
    decreases right.len(),
{
    reveal_with_fuel(reference_count, 2);
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        reference_count_add(left, right.drop_last(), reference);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// Moving beneath any owner changes only paths, including fixed capture fields
/// and runtime container indices. It cannot clone or retire a target identity.
pub proof fn reference_count_prefix(memory: Seq<Record>, path: Seq<int>, reference: Reference)
    ensures
        reference_count(prefix(memory, path), reference) == reference_count(memory, reference),
    decreases memory.len(),
{
    reveal_with_fuel(reference_count, 2);
    reveal_with_fuel(prefix, 2);
    if memory.len() > 0 {
        reference_count_prefix(memory.drop_last(), path, reference);
        let mapped = Record { path: path + memory.last().path, ..memory.last() };
        assert(prefix(memory, path).drop_last() =~= prefix(memory.drop_last(), path));
        assert(prefix(memory, path).last() == mapped);
    }
}

/// Extracting one child partitions its reference multiset. The caller must
/// execute actual drop/join effects to retire any extracted references.
pub proof fn reference_count_partition(memory: Seq<Record>, path: Seq<int>, reference: Reference)
    ensures
        reference_count(memory, reference) == reference_count(subtree(memory, path), reference)
            + reference_count(without(memory, path), reference),
    decreases memory.len(),
{
    reveal_with_fuel(reference_count, 2);
    reveal_with_fuel(subtree, 2);
    reveal_with_fuel(without, 2);
    if memory.len() > 0 {
        reference_count_partition(memory.drop_last(), path, reference);
        if path.is_prefix_of(memory.last().path) {
            assert(subtree(memory, path).drop_last() =~= subtree(memory.drop_last(), path));
        } else {
            assert(without(memory, path).drop_last() =~= without(memory.drop_last(), path));
        }
    }
}

/// Each stored Arc owns one reservation on its observed allocation.
pub open spec fn shared_count(memory: Seq<Record>, root: int) -> int {
    reference_count(memory, Reference::Shared(seq![root]))
}

/// Dropping stored handles can only consume existing reservations.
pub proof fn shared_count_nonnegative(memory: Seq<Record>, root: int)
    ensures
        shared_count(memory, root) >= 0,
    decreases memory.len(),
{
    reveal(reference_count);
    if memory.len() > 0 {
        shared_count_nonnegative(memory.drop_last(), root);
    }
}

/// A newly created vector holds no references to any root.
pub proof fn shared_count_empty(root: int)
    ensures
        shared_count(Seq::empty(), root) == 0,
{
    reveal(reference_count);
}

/// A direct Arc slot contains exactly its identity record.
pub proof fn shared_count_slot(identity: int, root: int)
    ensures
        shared_count(seq![shared_reference(seq![], seq![identity])], root) == if identity == root {
            1int
        } else {
            0int
        },
{
    let leaf = seq![shared_reference(seq![], seq![identity])];
    reveal_with_fuel(reference_count, 2);
    if identity != root {
        assert(seq![identity][0] != seq![root][0]);
    }
}

/// Storing the child under a vector index preserves each root’s multiplicity.
pub proof fn shared_count_insert(memory: Seq<Record>, child: Seq<Record>, path: Seq<int>, root: int)
    ensures
        shared_count(memory + prefix(child, path), root) == shared_count(memory, root)
            + shared_count(child, root),
{
    let r = Reference::Shared(seq![root]);
    reference_count_add(memory, prefix(child, path), r);
    reference_count_prefix(child, path, r);
}

/// The popped slot and the remaining slots partition the old reservations.
/// The remainder supplies the lower bound when the extracted alias is dropped.
pub proof fn shared_count_pop(memory: Seq<Record>, path: Seq<int>, root: int)
    ensures
        shared_count(without(memory, path), root) >= 0,
        shared_count(memory, root) == shared_count(subtree(memory, path), root) + shared_count(
            without(memory, path),
            root,
        ),
{
    reference_count_partition(memory, path, Reference::Shared(seq![root]));
    shared_count_nonnegative(without(memory, path), root);
}

/// Reindexing a collection changes neither its links nor their multiplicity.
pub proof fn reference_count_shift(memory: Seq<Record>, base: int, reference: Reference)
    ensures
        reference_count(shift_children(memory, base), reference) == reference_count(
            memory,
            reference,
        ),
    decreases memory.len(),
{
    reveal_with_fuel(reference_count, 2);
    reveal_with_fuel(shift_children, 2);
    if memory.len() > 0 {
        reference_count_shift(memory.drop_last(), base, reference);
        assert(shift_children(memory, base).drop_last() =~= shift_children(
            memory.drop_last(),
            base,
        ));
    }
}

/// A repeated alias descriptor retains every strong handle, even though each
/// link's local byte charge is zero. Repetition alone does not mint aliases.
pub proof fn reference_count_repeat(
    child: Seq<Record>,
    start: int,
    count: int,
    reference: Reference,
)
    requires
        count >= 0,
    ensures
        reference_count(repeat(child, start, count), reference) == count * reference_count(
            child,
            reference,
        ),
    decreases count,
{
    reveal_with_fuel(repeat, 2);
    reveal(reference_count);
    if count > 0 {
        reference_count_repeat(child, start, count - 1, reference);
        let before = repeat(child, start, count - 1);
        let path = seq![start + count - 1];
        reference_count_prefix(child, path, reference);
        reference_count_add(before, prefix(child, path), reference);
        assert((count - 1) * reference_count(child, reference) + reference_count(child, reference)
            == count * reference_count(child, reference)) by (nonlinear_arith);
    } else {
        assert(count * reference_count(child, reference) == 0) by (nonlinear_arith)
            requires
                count == 0,
        ;
    }
}

/// Reference multiplicity of a generated collection. Builders may use their
/// iteration index in the target identity; they need not repeat one worker.
#[verifier::opaque]
pub open spec fn generated_reference_count(
    builder: spec_fn(int) -> Seq<Record>,
    count: int,
    reference: Reference,
) -> int
    decreases count,
{
    if count <= 0 {
        0
    } else {
        generated_reference_count(builder, count - 1, reference) + reference_count(
            builder(count - 1),
            reference,
        )
    }
}

/// Compose actual per-visit descriptors, preserving distinct worker indices and
/// repeated strong aliases. This theorem supplies no publication/completion fact.
pub proof fn reference_count_generate(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
    reference: Reference,
)
    requires
        count >= 0,
    ensures
        reference_count(generate_children(builder, width, count, start), reference)
            == generated_reference_count(builder, count, reference),
    decreases count,
{
    reveal_with_fuel(generate_children, 2);
    reveal_with_fuel(generated_reference_count, 2);
    reveal(reference_count);
    if count > 0 {
        reference_count_generate(builder, width, count - 1, start, reference);
        let before = generate_children(builder, width, count - 1, start);
        let block = builder(count - 1);
        let base = start + width * (count - 1);
        reference_count_shift(block, base, reference);
        reference_count_add(before, shift_children(block, base), reference);
    }
}

/// A checked uniform family contribution closes to a symbolic product. A
/// conditional/nonuniform publication keeps its generated sum instead.
pub proof fn generated_reference_count_uniform(
    builder: spec_fn(int) -> Seq<Record>,
    count: int,
    reference: Reference,
    per_visit: int,
)
    requires
        count >= 0,
        forall|index: int|
            0 <= index < count ==> reference_count(#[trigger] builder(index), reference)
                == per_visit,
    ensures
        generated_reference_count(builder, count, reference) == count * per_visit,
    decreases count,
{
    reveal_with_fuel(generated_reference_count, 2);
    if count > 0 {
        generated_reference_count_uniform(builder, count - 1, reference, per_visit);
        assert((count - 1) * per_visit + per_visit == count * per_visit) by (nonlinear_arith);
    } else {
        assert(count * per_visit == 0) by (nonlinear_arith)
            requires
                count == 0,
        ;
    }
}

/// One indexed publication has one exact handle identity, even when its family
/// contains many workers. This is distinct from the family's total population.
pub proof fn generated_reference_count_selected(
    builder: spec_fn(int) -> Seq<Record>,
    count: int,
    reference: Reference,
    selected: int,
)
    requires
        count >= 0,
        forall|index: int|
            0 <= index < count ==> reference_count(#[trigger] builder(index), reference) == if index
                == selected {
                1int
            } else {
                0int
            },
    ensures
        generated_reference_count(builder, count, reference) == if 0 <= selected < count {
            1int
        } else {
            0int
        },
    decreases count,
{
    reveal_with_fuel(generated_reference_count, 2);
    if count > 0 {
        generated_reference_count_selected(builder, count - 1, reference, selected);
        assert(reference_count(builder(count - 1), reference) == if count - 1 == selected {
            1int
        } else {
            0int
        });
    }
}

} // verus!
