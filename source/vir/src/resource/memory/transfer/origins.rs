//! Compose original allocation lifetimes separately from local charge forests.

use super::{
    Origins,
    checked::{CallOrigins, OriginSource, OriginTarget, Place},
};
use crate::ast::*;
use crate::resource::memory::{analysis::Analysis, heap::Owner, model::unsupported};
use std::collections::BTreeMap;

impl Analysis<'_> {
    /// Borrowed runtime inputs need structural provenance even though their
    /// original bytes stay in the caller's live storage throughout this call.
    pub(in super::super) fn mark_borrowed_origins(
        &mut self,
        function: &Function,
    ) -> Result<(), VirErr> {
        if !super::required(function, self.layouts)? {
            return Ok(());
        }
        for (parameter, value) in function.x.params.iter().enumerate() {
            let Some(mut owner) = self.heap.borrowed.remove(&value.x.name) else { continue };
            let mut paths = Vec::new();
            owner.visit_paths(&mut vec![], &mut |path, _| paths.push(path.clone()));
            for path in paths {
                let id = self.transitions.fresh_region();
                self.transitions.borrowed_inputs.insert(id, (parameter, path.clone()));
                self.storage.add_input(id);
                owner.at_mut(&path).unwrap().input = Some(id);
            }
            self.heap.borrowed.insert(value.x.name.clone(), owner);
        }
        Ok(())
    }

    /// Record output identities while the accounting owners still retain them.
    /// The checked evaluator later supplies their original-only expressions.
    pub(in super::super) fn record_output_origins(
        &mut self,
        function: &Function,
        result: Option<&Owner>,
    ) {
        let collect = |owner: &Owner| {
            let mut paths = BTreeMap::new();
            owner.visit_paths(&mut vec![], &mut |path, node| {
                if let Some(id) = node.input {
                    paths.insert(path.clone(), id);
                }
            });
            paths
        };
        let mut outputs = Origins::new();
        if let Some(owner) = result {
            outputs.insert(None, collect(owner));
        }
        for (index, parameter) in function.x.params.iter().enumerate() {
            if let Some(owner) = self.heap.borrowed.get(&parameter.x.name) {
                outputs.insert(Some(index), collect(owner));
            }
        }
        self.transitions.outputs = outputs;
    }

    /// Capture disjoint origins before argument evaluation consumes any owner.
    pub(super) fn prepare_call_origins(
        &self,
        function: &Function,
        args: &Exprs,
        owners: &BTreeMap<usize, Owner>,
    ) -> CallOrigins {
        let mut result = CallOrigins::default();
        for (index, owner) in owners {
            let mut sources = Vec::new();
            owner.visit_paths(&mut vec![], &mut |path, node| {
                if let Some(input) = node.input {
                    sources.push(OriginSource { input, path: path.clone(), selection: None });
                }
            });
            let typ = self
                .layouts
                .borrowed_owner(&function.x.params[*index].x.typ)
                .unwrap_or(&function.x.params[*index].x.typ);
            if sources.is_empty() {
                if let Some((name, path)) = crate::resource::memory::paths::expr(&args[*index], typ)
                {
                    let root = self.heap.root(&name).unwrap();
                    if let Some((depth, input)) = (0..path.len()).rev().find_map(|depth| {
                        // Fixed nodes have independent regions. Only runtime
                        // descendants belong to an enclosing node's region.
                        if !matches!(path[depth], super::super::heap::OwnerSlot::Element(_)) {
                            return None;
                        }
                        root.at(&path[..depth])?.input.map(|input| (depth, input))
                    }) {
                        sources.push(OriginSource {
                            input,
                            path: vec![],
                            selection: Some((
                                Place {
                                    source: args[*index].clone(),
                                    typ: typ.clone(),
                                    location: (name, path),
                                },
                                depth,
                            )),
                        });
                    }
                }
            }
            result.sources.insert(*index, sources);
        }
        result
    }

    /// Attach a callee output's original regions once, independently of newly
    /// retained allocation charges. An indexed loan updates its enclosing region.
    pub(super) fn apply_call_origins(
        &mut self,
        function: &Function,
        args: &Exprs,
        target: Option<usize>,
        owner: &mut Owner,
        origins: &mut CallOrigins,
    ) -> Result<(), VirErr> {
        if origins.sources.values().all(Vec::is_empty) {
            return Ok(());
        }
        let template = self.summaries[&function.x.name].transfer.as_ref().unwrap();
        let Some(paths) = template.origins.get(&target) else {
            return Ok(());
        };
        let ancestor = target
            .and_then(|index| origins.sources.get(&index))
            .and_then(|sources| sources.iter().find(|source| source.selection.is_some()))
            .cloned();
        if let Some(ancestor) = ancestor {
            let (place, depth) = ancestor.selection.as_ref().unwrap();
            self.heap.check_partition(&place.location.0, &args[target.unwrap()].span)?;
            let id = self.transitions.fresh_region();
            let parent = self
                .heap
                .root_mut(&place.location.0)
                .unwrap()
                .at_mut(&place.location.1[..*depth])
                .unwrap();
            parent.input = Some(id);
            self.storage.release_input(ancestor.input);
            self.storage.add_input(id);
            origins.targets.insert(
                id,
                OriginTarget { parameter: target, path: None, ancestor: Some(ancestor) },
            );
            return Ok(());
        }
        for path in paths.keys() {
            let node = owner.at_mut(path).ok_or_else(|| {
                unsupported(&function.span, "an original output without its fixed ownership node")
            })?;
            if let Some(old) = node.input.take() {
                self.storage.release_input(old);
            }
            let id = self.transitions.fresh_region();
            self.storage.add_input(id);
            node.input = Some(id);
            origins.targets.insert(
                id,
                OriginTarget { parameter: target, path: Some(path.clone()), ancestor: None },
            );
        }
        Ok(())
    }
}
