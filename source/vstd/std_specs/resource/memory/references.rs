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
    /// All handles whose identity consists of this family followed by one index.
    /// This query cannot construct a handle or establish worker completion.
    WorkerFamily(Seq<int>),
}

/// A strong handle's owner node has no separate byte charge. Its inline slot
/// belongs to its containing value, and backing storage belongs to the root.
pub open spec fn shared_reference(path: Seq<int>, identity: Seq<int>) -> Record {
    Record { reference_kind: 1, reference_identity: identity, ..super::forest::empty_record(path) }
}

/// Join-handle ownership names a worker independently of the source handle slot.
pub open spec fn worker_reference(path: Seq<int>, identity: Seq<int>) -> Record {
    Record { reference_kind: 2, reference_identity: identity, ..super::forest::empty_record(path) }
}

/// Query links without adding nested datatype invariants to every byte record.
pub open spec fn refers_to(record: Record, reference: Reference) -> bool {
    match reference {
        Reference::Shared(identity) => record.reference_kind == 1 && record.reference_identity
            == identity,
        Reference::Worker(identity) => record.reference_kind == 2 && record.reference_identity
            == identity,
        Reference::WorkerFamily(family) => record.reference_kind == 2
            && record.reference_identity.len() == family.len() + 1 && family.is_prefix_of(
            record.reference_identity,
        ),
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

} // verus!
