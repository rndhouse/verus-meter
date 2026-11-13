//! Generated and tiled child blocks with checked widths, costs, and indexed views.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::cost::{cost, cost_add, cost_empty};
#[cfg(verus_keep_ghost)]
use super::forest::{
    Record, contains, descendants, nonruntime, prefix, runtime, runtime_add, runtime_class,
    subtree, well_formed, well_formed_add, without,
};
#[cfg(verus_keep_ghost)]
use super::ranges::{repeat, shift_children, shift_children_facts, shift_children_select};
#[cfg(verus_keep_ghost)]
use super::selection::{descendants_add, select_add, select_empty, slot_prefix};
#[cfg(verus_keep_ghost)]
use super::views::view_requested;

verus! {

broadcast use crate::seq::group_seq_axioms;

/// Repeat an ordered block of runtime children, flattening its logical indices.
/// Width counts occupied children independently of the block's allocation cost.
#[verifier::opaque]
pub open spec fn tile_children(block: Seq<Record>, width: int, count: int, start: int) -> Seq<
    Record,
>
    decreases count,
{
    if count <= 0 {
        Seq::empty()
    } else {
        tile_children(block, width, count - 1, start) + shift_children(
            block,
            start + width * (count - 1),
        )
    }
}

/// Block repetition preserves every child descriptor and has additive cost.
pub proof fn tile_children_facts(block: Seq<Record>, width: int, count: int, start: int)
    requires
        well_formed(block),
        width >= 0,
        count >= 0,
        start >= 0,
        runtime(block) == block,
    ensures
        well_formed(tile_children(block, width, count, start)),
        cost(tile_children(block, width, count, start), 0) == count * cost(block, 0),
        runtime(tile_children(block, width, count, start)) == tile_children(
            block,
            width,
            count,
            start,
        ),
        nonruntime(tile_children(block, width, count, start)) == Seq::<Record>::empty(),
        descendants(tile_children(block, width, count, start)) == tile_children(
            block,
            width,
            count,
            start,
        ),
    decreases count,
{
    reveal_with_fuel(tile_children, 2);
    if count > 0 {
        tile_children_facts(block, width, count - 1, start);
        let base = start + width * (count - 1);
        assert(width * (count - 1) >= 0) by (nonlinear_arith)
            requires
                width >= 0,
                count > 0,
        ;
        assert(base >= 0);
        shift_children_facts(block, base);
        let before = tile_children(block, width, count - 1, start);
        let next = shift_children(block, base);
        well_formed_add(before, next);
        cost_add(before, next, 0);
        runtime_add(before, next);
        runtime_class(next);
        descendants_add(before, next);
        assert((count - 1) * cost(block, 0) + cost(block, 0) == count * cost(block, 0))
            by (nonlinear_arith);
        assert(cost(before, 0) + cost(next, 0) == count * cost(block, 0));
    } else {
        cost_empty(0);
    }
}

/// Generate a complete block for each iteration, preserving nonuniform children.
/// Logical width describes occupied slots independently of their allocation sizes.
#[verifier::opaque]
pub open spec fn generate_children(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
) -> Seq<Record>
    decreases count,
{
    if count <= 0 {
        Seq::empty()
    } else {
        generate_children(builder, width, count - 1, start) + shift_children(
            builder(count - 1),
            start + width * (count - 1),
        )
    }
}

/// Sum the actual footprint of every generated block, without a uniform bound.
#[verifier::opaque]
pub open spec fn generated_cost(builder: spec_fn(int) -> Seq<Record>, count: int) -> int
    decreases count,
{
    if count <= 0 {
        0
    } else {
        generated_cost(builder, count - 1) + cost(builder(count - 1), 0)
    }
}

/// Sum an affine footprint over any number of generated iterations. Doubling
/// the sum avoids division and preserves an exact integer equality.
pub proof fn generated_cost_affine(
    builder: spec_fn(int) -> Seq<Record>,
    count: int,
    slope: int,
    intercept: int,
)
    requires
        count >= 0,
        forall|k: int| 0 <= k < count ==> cost(#[trigger] builder(k), 0) == slope * k + intercept,
    ensures
        2 * generated_cost(builder, count) == slope * count * (count - 1) + 2 * intercept * count,
    decreases count,
{
    reveal_with_fuel(generated_cost, 2);
    if count > 0 {
        generated_cost_affine(builder, count - 1, slope, intercept);
        let previous = generated_cost(builder, count - 1);
        let current = generated_cost(builder, count);
        assert(2 * current == slope * count * (count - 1) + 2 * intercept * count)
            by (nonlinear_arith)
            requires
                2 * previous == slope * (count - 1) * (count - 2) + 2 * intercept * (count - 1),
                current == previous + slope * (count - 1) + intercept,
        ;
    } else {
        assert(slope * count * (count - 1) + 2 * intercept * count == 0) by (nonlinear_arith)
            requires
                count == 0,
        ;
    }
}

/// Generation preserves validity and adds the exact costs of different blocks.
pub proof fn generate_children_facts(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
)
    requires
        width >= 0,
        count >= 0,
        start >= 0,
        forall|k: int| 0 <= k < count ==> well_formed(#[trigger] builder(k)),
        forall|k: int| 0 <= k < count ==> runtime(#[trigger] builder(k)) == builder(k),
    ensures
        well_formed(generate_children(builder, width, count, start)),
        cost(generate_children(builder, width, count, start), 0) == generated_cost(builder, count),
        runtime(generate_children(builder, width, count, start)) == generate_children(
            builder,
            width,
            count,
            start,
        ),
        nonruntime(generate_children(builder, width, count, start)) == Seq::<Record>::empty(),
        descendants(generate_children(builder, width, count, start)) == generate_children(
            builder,
            width,
            count,
            start,
        ),
    decreases count,
{
    reveal_with_fuel(generate_children, 2);
    reveal_with_fuel(generated_cost, 2);
    if count > 0 {
        generate_children_facts(builder, width, count - 1, start);
        let block = builder(count - 1);
        let base = start + width * (count - 1);
        assert(base >= 0) by (nonlinear_arith)
            requires
                start >= 0,
                width >= 0,
                count > 0,
                base == start + width * (count - 1),
        ;
        shift_children_facts(block, base);
        let before = generate_children(builder, width, count - 1, start);
        let next = shift_children(block, base);
        well_formed_add(before, next);
        cost_add(before, next, 0);
        runtime_add(before, next);
        runtime_class(next);
        descendants_add(before, next);
    } else {
        cost_empty(0);
    }
}

/// Every descriptor in an ordered block belongs to one occupied runtime slot.
pub open spec fn block_bounds(memory: Seq<Record>, width: int) -> bool
    decreases memory.len(),
{
    memory.len() == 0 || (block_bounds(memory.drop_last(), width) && memory.last().path.len() > 0
        && 0 <= memory.last().path[0] < width)
}

/// A complete child occupies one declared slot in a block.
pub proof fn block_bounds_prefix(child: Seq<Record>, index: int, width: int)
    requires
        0 <= index < width,
    ensures
        block_bounds(prefix(child, seq![index]), width),
    decreases child.len(),
{
    reveal_with_fuel(prefix, 2);
    if child.len() > 0 {
        block_bounds_prefix(child.drop_last(), index, width);
        let before = prefix(child.drop_last(), seq![index]);
        let value = Record { path: seq![index] + child.last().path, ..child.last() };
        assert(before.push(value).drop_last() =~= before);
    }
}

/// Composing forests preserves their common logical block extent.
pub proof fn block_bounds_add(left: Seq<Record>, right: Seq<Record>, width: int)
    requires
        block_bounds(left, width),
        block_bounds(right, width),
    ensures
        block_bounds(left + right, width),
    decreases right.len(),
{
    if right.len() == 0 {
        assert(left + right =~= left);
    } else {
        block_bounds_add(left, right.drop_last(), width);
        assert((left + right).drop_last() =~= left + right.drop_last());
    }
}

/// A wider logical extent still contains every descriptor.
pub proof fn block_bounds_weaken(memory: Seq<Record>, from: int, to: int)
    requires
        block_bounds(memory, from),
        from <= to,
    ensures
        block_bounds(memory, to),
    decreases memory.len(),
{
    if memory.len() > 0 {
        block_bounds_weaken(memory.drop_last(), from, to);
    }
}

/// Translating runtime indices translates the block extent.
pub proof fn block_bounds_shift(memory: Seq<Record>, width: int, base: int)
    requires
        block_bounds(memory, width),
        base >= 0,
    ensures
        block_bounds(shift_children(memory, base), base + width),
    decreases memory.len(),
{
    reveal_with_fuel(shift_children, 2);
    if memory.len() > 0 {
        block_bounds_shift(memory.drop_last(), width, base);
        let before = shift_children(memory.drop_last(), base);
        let value = Record {
            path: memory.last().path.update(0, memory.last().path[0] + base),
            ..memory.last()
        };
        assert(before.push(value).drop_last() =~= before);
    }
}

/// Consecutive copies remain inside the declared logical extent.
pub proof fn block_bounds_repeat(child: Seq<Record>, start: int, count: int, width: int)
    requires
        start >= 0,
        count >= 0,
        start + count <= width,
    ensures
        block_bounds(repeat(child, start, count), width),
    decreases count,
{
    reveal_with_fuel(repeat, 2);
    if count > 0 {
        block_bounds_repeat(child, start, count - 1, width);
        block_bounds_prefix(child, start + count - 1, width);
        block_bounds_add(
            repeat(child, start, count - 1),
            prefix(child, seq![start + count - 1]),
            width,
        );
    }
}

/// Flattened repeated blocks occupy their combined logical extent.
pub proof fn block_bounds_tile(block: Seq<Record>, width: int, count: int, start: int)
    requires
        block_bounds(block, width),
        width >= 0,
        count >= 0,
        start >= 0,
    ensures
        block_bounds(tile_children(block, width, count, start), start + width * count),
    decreases count,
{
    reveal_with_fuel(tile_children, 2);
    if count > 0 {
        block_bounds_tile(block, width, count - 1, start);
        let base = start + width * (count - 1);
        assert(base >= 0 && base <= start + width * count && base + width == start + width * count)
            by (nonlinear_arith)
            requires
                start >= 0,
                width >= 0,
                count > 0,
                base == start + width * (count - 1),
        ;
        block_bounds_weaken(
            tile_children(block, width, count - 1, start),
            base,
            start + width * count,
        );
        block_bounds_shift(block, width, base);
        block_bounds_add(
            tile_children(block, width, count - 1, start),
            shift_children(block, base),
            start + width * count,
        );
    }
}

/// Indices outside a block select no child allocations.
pub proof fn block_bounds_empty_selection(memory: Seq<Record>, width: int, index: int)
    requires
        block_bounds(memory, width),
        index < 0 || index >= width,
    ensures
        subtree(memory, seq![index]) == Seq::<Record>::empty(),
    decreases memory.len(),
{
    reveal_with_fuel(subtree, 2);
    if memory.len() > 0 {
        block_bounds_empty_selection(memory.drop_last(), width, index);
        slot_prefix(index, memory.last().path);
    }
}

/// Indices outside the repeated block range select an empty forest.
pub proof fn tile_children_outside(
    block: Seq<Record>,
    width: int,
    count: int,
    start: int,
    index: int,
)
    requires
        block_bounds(block, width),
        width >= 0,
        count >= 0,
        start >= 0,
        index < start || index >= start + width * count,
    ensures
        subtree(tile_children(block, width, count, start), seq![index]) == Seq::<Record>::empty(),
    decreases count,
{
    reveal_with_fuel(tile_children, 2);
    if count > 0 {
        let base = start + width * (count - 1);
        assert(base >= 0 && base <= start + width * count && base + width == start + width * count)
            by (nonlinear_arith)
            requires
                start >= 0,
                width >= 0,
                count > 0,
                base == start + width * (count - 1),
        ;
        tile_children_outside(block, width, count - 1, start, index);
        shift_children_select(block, width, base, index);
        block_bounds_empty_selection(block, width, index - base);
        select_add(
            tile_children(block, width, count - 1, start),
            shift_children(block, base),
            seq![index],
        );
    } else {
        select_empty(seq![index]);
    }
}

/// Select one logical slot without expanding the number of repetitions.
pub proof fn tile_children_at(
    block: Seq<Record>,
    width: int,
    count: int,
    start: int,
    iteration: int,
    offset: int,
)
    requires
        block_bounds(block, width),
        width > 0,
        count >= 0,
        start >= 0,
        0 <= iteration < count,
        0 <= offset < width,
    ensures
        subtree(tile_children(block, width, count, start), seq![start + width * iteration + offset])
            == subtree(block, seq![offset]),
    decreases count,
{
    reveal_with_fuel(tile_children, 2);
    let index = start + width * iteration + offset;
    let base = start + width * (count - 1);
    assert(base >= 0) by (nonlinear_arith)
        requires
            start >= 0,
            width > 0,
            count > 0,
            base == start + width * (count - 1),
    ;
    shift_children_select(block, width, base, index);
    select_add(
        tile_children(block, width, count - 1, start),
        shift_children(block, base),
        seq![index],
    );
    if iteration == count - 1 {
        assert(index == base + offset) by (nonlinear_arith)
            requires
                iteration == count - 1,
                index == start + width * iteration + offset,
                base == start + width * (count - 1),
        ;
        tile_children_outside(block, width, count - 1, start, index);
    } else {
        tile_children_at(block, width, count - 1, start, iteration, offset);
        assert(index - base < 0) by (nonlinear_arith)
            requires
                width > 0,
                0 <= offset < width,
                iteration < count - 1,
                index == start + width * iteration + offset,
                base == start + width * (count - 1),
        ;
        block_bounds_empty_selection(block, width, index - base);
    }
}

/// Exact indexed views avoid expanding a runtime number of blocks at callers.
pub proof fn tile_children_views(block: Seq<Record>, width: int, count: int, start: int)
    requires
        block_bounds(block, width),
        width >= 0,
        count >= 0,
        start >= 0,
    ensures
        forall|index: int|
            #![trigger view_requested(tile_children(block, width, count, start), index), subtree(tile_children(block, width, count, start), seq![index])]
            view_requested(tile_children(block, width, count, start), index) ==> (subtree(
                tile_children(block, width, count, start),
                seq![index],
            ) == if width > 0 && start <= index < start + width * count {
                subtree(block, seq![(index - start) % width])
            } else {
                Seq::<Record>::empty()
            }),
{
    assert forall|index: int|
        #![trigger view_requested(tile_children(block, width, count, start), index), subtree(tile_children(block, width, count, start), seq![index])]
        view_requested(tile_children(block, width, count, start), index) ==> (subtree(
            tile_children(block, width, count, start),
            seq![index],
        ) == if width > 0 && start <= index < start + width * count {
            subtree(block, seq![(index - start) % width])
        } else {
            Seq::<Record>::empty()
        }) by {
        if width > 0 && start <= index < start + width * count {
            let x = index - start;
            let k = x / width;
            let r = x % width;
            crate::arithmetic::div_mod::lemma_fundamental_div_mod(x, width);
            crate::arithmetic::div_mod::lemma_mod_pos_bound(x, width);
            assert(0 <= k < count) by (nonlinear_arith)
                requires
                    x == width * k + r,
                    0 <= r < width,
                    width > 0,
                    0 <= x < width * count,
            ;
            tile_children_at(block, width, count, start, k, r);
            assert(index == start + width * k + r);
        } else {
            tile_children_outside(block, width, count, start, index);
        }
    }
}

/// Flattened repeated blocks occupy their combined logical extent.
pub proof fn block_bounds_generate(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
)
    requires
        forall|k: int| 0 <= k < count ==> block_bounds(#[trigger] builder(k), width),
        width >= 0,
        count >= 0,
        start >= 0,
    ensures
        block_bounds(generate_children(builder, width, count, start), start + width * count),
    decreases count,
{
    reveal_with_fuel(generate_children, 2);
    if count > 0 {
        block_bounds_generate(builder, width, count - 1, start);
        let base = start + width * (count - 1);
        assert(base >= 0 && base <= start + width * count && base + width == start + width * count)
            by (nonlinear_arith)
            requires
                start >= 0,
                width >= 0,
                count > 0,
                base == start + width * (count - 1),
        ;
        block_bounds_weaken(
            generate_children(builder, width, count - 1, start),
            base,
            start + width * count,
        );
        block_bounds_shift(builder(count - 1), width, base);
        block_bounds_add(
            generate_children(builder, width, count - 1, start),
            shift_children(builder(count - 1), base),
            start + width * count,
        );
    }
}

/// Indices outside the repeated block range select an empty forest.
pub proof fn generate_children_outside(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
    index: int,
)
    requires
        forall|k: int| 0 <= k < count ==> block_bounds(#[trigger] builder(k), width),
        width >= 0,
        count >= 0,
        start >= 0,
        index < start || index >= start + width * count,
    ensures
        subtree(generate_children(builder, width, count, start), seq![index]) == Seq::<
            Record,
        >::empty(),
    decreases count,
{
    reveal_with_fuel(generate_children, 2);
    if count > 0 {
        let base = start + width * (count - 1);
        assert(base >= 0 && base <= start + width * count && base + width == start + width * count)
            by (nonlinear_arith)
            requires
                start >= 0,
                width >= 0,
                count > 0,
                base == start + width * (count - 1),
        ;
        generate_children_outside(builder, width, count - 1, start, index);
        shift_children_select(builder(count - 1), width, base, index);
        block_bounds_empty_selection(builder(count - 1), width, index - base);
        select_add(
            generate_children(builder, width, count - 1, start),
            shift_children(builder(count - 1), base),
            seq![index],
        );
    } else {
        select_empty(seq![index]);
    }
}

/// Select one logical slot without expanding the number of repetitions.
pub proof fn generate_children_at(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
    iteration: int,
    offset: int,
)
    requires
        forall|k: int| 0 <= k < count ==> block_bounds(#[trigger] builder(k), width),
        width > 0,
        count >= 0,
        start >= 0,
        0 <= iteration < count,
        0 <= offset < width,
    ensures
        subtree(
            generate_children(builder, width, count, start),
            seq![start + width * iteration + offset],
        ) == subtree(builder(iteration), seq![offset]),
    decreases count,
{
    reveal_with_fuel(generate_children, 2);
    let index = start + width * iteration + offset;
    let base = start + width * (count - 1);
    assert(base >= 0) by (nonlinear_arith)
        requires
            start >= 0,
            width > 0,
            count > 0,
            base == start + width * (count - 1),
    ;
    shift_children_select(builder(count - 1), width, base, index);
    select_add(
        generate_children(builder, width, count - 1, start),
        shift_children(builder(count - 1), base),
        seq![index],
    );
    if iteration == count - 1 {
        assert(index == base + offset) by (nonlinear_arith)
            requires
                iteration == count - 1,
                index == start + width * iteration + offset,
                base == start + width * (count - 1),
        ;
        generate_children_outside(builder, width, count - 1, start, index);
    } else {
        generate_children_at(builder, width, count - 1, start, iteration, offset);
        assert(index - base < 0) by (nonlinear_arith)
            requires
                width > 0,
                0 <= offset < width,
                iteration < count - 1,
                index == start + width * iteration + offset,
                base == start + width * (count - 1),
        ;
        block_bounds_empty_selection(builder(count - 1), width, index - base);
    }
}

/// Exact indexed views avoid expanding a runtime number of blocks at callers.
pub proof fn generate_children_views(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
)
    requires
        forall|k: int| 0 <= k < count ==> block_bounds(#[trigger] builder(k), width),
        width >= 0,
        count >= 0,
        start >= 0,
    ensures
        forall|index: int|
            #![trigger view_requested(generate_children(builder, width, count, start), index), subtree(generate_children(builder, width, count, start), seq![index])]
            view_requested(generate_children(builder, width, count, start), index) ==> (subtree(
                generate_children(builder, width, count, start),
                seq![index],
            ) == if width > 0 && start <= index < start + width * count {
                subtree(builder((index - start) / width), seq![(index - start) % width])
            } else {
                Seq::<Record>::empty()
            }),
{
    assert forall|index: int|
        #![trigger view_requested(generate_children(builder, width, count, start), index), subtree(generate_children(builder, width, count, start), seq![index])]
        view_requested(generate_children(builder, width, count, start), index) ==> (subtree(
            generate_children(builder, width, count, start),
            seq![index],
        ) == if width > 0 && start <= index < start + width * count {
            subtree(builder((index - start) / width), seq![(index - start) % width])
        } else {
            Seq::<Record>::empty()
        }) by {
        if width > 0 && start <= index < start + width * count {
            let x = index - start;
            let k = x / width;
            let r = x % width;
            crate::arithmetic::div_mod::lemma_fundamental_div_mod(x, width);
            crate::arithmetic::div_mod::lemma_mod_pos_bound(x, width);
            assert(0 <= k < count) by (nonlinear_arith)
                requires
                    x == width * k + r,
                    0 <= r < width,
                    width > 0,
                    0 <= x < width * count,
            ;
            generate_children_at(builder, width, count, start, k, r);
            assert(index == start + width * k + r);
        } else {
            assert(index < start || index >= start + width * count) by (nonlinear_arith)
                requires
                    width >= 0,
                    !(width > 0 && start <= index < start + width * count),
            ;
            generate_children_outside(builder, width, count, start, index);
        }
    }
}

} // verus!
