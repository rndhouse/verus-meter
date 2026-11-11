//! Incoming lifetime regions follow the same partitions as physical ownership.
//! They retain original input descriptors only; helper-created storage remains
//! in the ordinary body charge, so it cannot be counted again at the caller.

use super::*;
use crate::resource::memory::metadata::operations::{Removal, replace};

impl Trace<'_> {
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

    pub(super) fn split_region(
        &mut self,
        span: &Span,
        location: &Location,
        removal: &Removal,
        input: &checked::InputSplit,
    ) -> Option<()> {
        let mut memory = self.regions.get(&input.source)?.clone();
        let mut parents = Vec::new();
        for step in location.2.get(input.depth..)? {
            let path = Self::path(span, std::slice::from_ref(step));
            parents.push((memory.clone(), path.clone()));
            memory = expr::subtree(span, memory, path);
        }
        let partition = removal.partition(span, memory);
        let remaining =
            parents.into_iter().rev().fold(partition.remaining, |memory, (parent, path)| {
                replace(span, parent, path, memory)
            });
        self.regions.insert(input.remaining, simplify::simplify(&remaining));
        for (path, id) in &input.selected {
            let mut memory = path.iter().fold(partition.selected.clone(), |memory, slot| {
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
        Some(())
    }
}
