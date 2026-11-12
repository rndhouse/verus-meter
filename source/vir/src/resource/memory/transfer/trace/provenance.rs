//! Incoming lifetime regions follow the same partitions as physical ownership.
//! They retain original input descriptors only; helper-created storage remains
//! in the ordinary body charge, so it cannot be counted again at the caller.

use super::*;
use crate::resource::memory::metadata::operations::{Partition, replace};

impl Trace<'_> {
    pub(super) fn original_child(&self, span: &Span, input: &checked::InputJoin) -> Option<Expr> {
        let mut child = expr::empty(span, expr::record_type());
        for (path, id) in &input.children {
            child = expr::add(
                span,
                child,
                expr::prefix(
                    span,
                    self.regions.get(id)?.clone(),
                    expr::path(span, path.iter().map(|slot| self.layouts.metadata_slot(slot))),
                ),
            );
        }
        Some(simplify::simplify(&child))
    }

    pub(super) fn join_region(
        &mut self,
        span: &Span,
        index: Expr,
        input: &checked::InputJoin,
    ) -> Option<()> {
        let child = self.original_child(span, input)?;
        let parent = match input.previous {
            Some(id) => self.regions.get(&id)?.clone(),
            None => expr::empty(span, expr::record_type()),
        };
        let joined = expr::add(
            span,
            parent,
            expr::prefix(span, child, expr::push(span, expr::path(span, []), index)),
        );
        self.regions.insert(input.result, simplify::simplify(&joined));
        Some(())
    }

    /// Replacement releases the selected original subtree, without inserting
    /// the new child's local charges into an incoming lifetime region.
    pub(super) fn replace_region(
        &mut self,
        span: &Span,
        location: &Location,
        input: &checked::InputSplit,
    ) -> Option<()> {
        self.partition_region(span, location, input, |memory| {
            crate::resource::memory::metadata::operations::detach(
                span,
                memory,
                expr::path(span, []),
            )
        })
    }

    pub(super) fn initialize_regions(&mut self, function: &Function) -> Option<()> {
        for (id, (parameter, path)) in self.checked.inputs.iter().enumerate() {
            let Value::Owner(node) =
                self.state.values.get(&function.x.params[*parameter].x.name)?
            else {
                return None;
            };
            let mut memory = node.memory.clone();
            for slot in path {
                memory = expr::subtree(
                    &function.span,
                    memory,
                    expr::path(&function.span, [self.layouts.metadata_slot(slot)]),
                );
            }
            // An input identity covers one fixed node and its runtime descendants.
            // The input table gives fixed children their own disjoint identities.
            for (_, child_path) in self.checked.inputs.iter().filter(|(p, child)| {
                p == parameter && child.len() == path.len() + 1 && child.starts_with(path)
            }) {
                memory = expr::without(
                    &function.span,
                    memory,
                    expr::path(&function.span, [self.layouts.metadata_slot(child_path.last()?)]),
                );
            }
            self.regions.insert(id, simplify::simplify(&memory));
        }
        Some(())
    }

    pub(super) fn partition_region(
        &mut self,
        span: &Span,
        location: &Location,
        input: &checked::InputSplit,
        partition: impl FnOnce(Expr) -> Partition,
    ) -> Option<()> {
        self.partition_region_selected(span, location, input, partition, None).map(|_| ())
    }

    pub(super) fn partition_region_selected(
        &mut self,
        span: &Span,
        location: &Location,
        input: &checked::InputSplit,
        partition: impl FnOnce(Expr) -> Partition,
        selected: Option<Expr>,
    ) -> Option<Expr> {
        let mut memory = self.regions.get(&input.source)?.clone();
        let mut parents = Vec::new();
        for step in location.2.get(input.depth..)? {
            let path = Self::path(span, std::slice::from_ref(step));
            parents.push((memory.clone(), path.clone()));
            memory = expr::subtree(span, memory, path);
        }
        let partition = partition(memory);
        let remaining =
            parents.into_iter().rev().fold(partition.remaining, |memory, (parent, path)| {
                replace(span, parent, path, memory)
            });
        self.regions.insert(input.remaining, simplify::simplify(&remaining));
        let witness = partition.selected;
        let selected = selected.unwrap_or_else(|| witness.clone());
        for (path, id) in &input.selected {
            let mut memory = path.iter().fold(selected.clone(), |memory, slot| {
                expr::subtree(span, memory, expr::path(span, [self.layouts.metadata_slot(slot)]))
            });
            for child in input
                .selected
                .keys()
                .filter(|child| child.len() == path.len() + 1 && child.starts_with(path))
            {
                memory = expr::without(
                    span,
                    memory,
                    expr::path(span, [self.layouts.metadata_slot(child.last()?)]),
                );
            }
            self.regions.insert(*id, simplify::simplify(&memory));
        }
        Some(witness)
    }
}
