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
        location: &Location,
        index: Expr,
        input: &checked::InputJoin,
    ) -> Option<()> {
        let child = self.original_child(span, input)?;
        let parent = match input.previous {
            Some(id) => self.regions.get(&id)?.clone(),
            None => expr::empty(span, expr::record_type()),
        };
        let path = Self::path(span, location.2.get(input.depth..)?);
        let selected = expr::subtree(span, parent.clone(), path.clone());
        let joined = expr::add(
            span,
            selected,
            expr::prefix(span, child, expr::push(span, expr::path(span, []), index)),
        );
        self.regions.insert(input.result, simplify::simplify(&replace(span, parent, path, joined)));
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
        for (id, (parameter, path)) in self
            .checked
            .inputs
            .iter()
            .enumerate()
            .chain(self.checked.borrowed_inputs.iter().map(|(id, path)| (*id, path)))
        {
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
            for (_, child_path) in
                self.checked.inputs.iter().chain(self.checked.borrowed_inputs.values()).filter(
                    |(p, child)| {
                        p == parameter && child.len() == path.len() + 1 && child.starts_with(path)
                    },
                )
            {
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

impl Trace<'_> {
    /// Resolve a caller region before the callee mutates any argument forest.
    fn call_origin_source(&mut self, span: &Span, source: &checked::OriginSource) -> Option<Expr> {
        let mut memory = self.regions.get(&source.input)?.clone();
        if let Some((place, depth)) = &source.selection {
            let location = self.checked_location(place)?;
            memory = expr::subtree(span, memory, Self::path(span, location.2.get(*depth..)?));
        }
        Some(memory)
    }

    /// Specialize original-only regions for intermediate peaks and final owners.
    /// Physical geometry drives decisions; fresh allocations stay separate.
    pub(super) fn compose_call_origins(
        &mut self,
        value: &Expr,
        function: &Function,
        template: &Template,
        physical: &HashMap<VarIdent, Expr>,
        call: &checked::CallOrigins,
    ) -> Option<()> {
        if call.targets.is_empty() && call.peaks.is_empty() {
            return Some(());
        }
        let span = &value.span;
        let mut forests = BTreeMap::new();
        for (index, sources) in &call.sources {
            let mut memory = expr::empty(span, expr::record_type());
            for source in sources {
                let selected = self.call_origin_source(span, source)?;
                memory = expr::add(
                    span,
                    memory,
                    expr::prefix(
                        span,
                        selected,
                        expr::path(
                            span,
                            source.path.iter().map(|slot| self.layouts.metadata_slot(slot)),
                        ),
                    ),
                );
            }
            forests.insert(*index, simplify::simplify(&memory));
        }
        let mut originals = physical.clone();
        let mut peaks = physical.clone();
        for symbol in &template.symbols {
            let (index, selected) = match &symbol.input {
                Input::Forest(index) => (*index, forests.get(index)?.clone()),
                Input::Property(index, path, "bytes") => {
                    let memory = expr::subtree(
                        span,
                        forests.get(index)?.clone(),
                        expr::path(span, path.iter().map(|slot| self.layouts.metadata_slot(slot))),
                    );
                    (*index, property(span, memory, "bytes"))
                }
                _ => continue,
            };
            originals.insert(symbol.name.clone(), selected.clone());
            let selected = if self.layouts.borrowed_owner(&function.x.params[index].x.typ).is_some()
            {
                match &symbol.input {
                    Input::Forest(_) => expr::empty(span, expr::record_type()),
                    _ => expr::integer(span, 0),
                }
            } else {
                selected
            };
            peaks.insert(symbol.name.clone(), selected);
        }
        for (callee, caller) in &call.peaks {
            self.regions.insert(*caller, substitute(template.regions.get(callee)?, &peaks));
        }
        for (id, target) in &call.targets {
            let paths = template.origins.get(&target.parameter)?;
            let memory = if let Some(path) = &target.path {
                substitute(paths.get(path)?, &originals)
            } else {
                let mut memory = expr::empty(span, expr::record_type());
                for (path, original) in paths {
                    memory = expr::add(
                        span,
                        memory,
                        expr::prefix(
                            span,
                            substitute(original, &originals),
                            expr::path(
                                span,
                                path.iter().map(|slot| self.layouts.metadata_slot(slot)),
                            ),
                        ),
                    );
                }
                memory
            };
            let memory = if let Some(ancestor) = &target.ancestor {
                let (place, depth) = ancestor.selection.as_ref()?;
                let location = self.checked_location(place)?;
                let parent = self.regions.get(&ancestor.input)?.clone();
                replace(span, parent, Self::path(span, location.2.get(*depth..)?), memory)
            } else {
                memory
            };
            self.regions.insert(*id, simplify::simplify(&memory));
        }
        Some(())
    }
}
