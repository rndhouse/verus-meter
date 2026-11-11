//! Partition incoming lifetimes independently of this frame's allocation charges.
//!
//! The body tracks identities, while the checked transfer evaluator supplies
//! their forest expressions. Each fixed node owns its descriptor and runtime
//! descendants; fixed children receive separate identities so partial drops
//! remain independent. Old identities survive in earlier peak profiles only.

use super::{analysis::Analysis, heap::Owner, transfer::checked::InputSplit};
use crate::{ast::VirErr, messages::Span};

impl Analysis<'_> {
    /// Snapshot potential conservation groups before the body changes counters.
    /// The checked iteration graph chooses groups later; every candidate remains
    /// an ordinary invariant proved at loop entry and on all back edges.
    pub(super) fn loop_charge_candidates(&mut self, span: &Span) -> Vec<crate::ast::Expr> {
        let mut roles = Vec::new();
        for (name, owner) in self.heap.owners.iter().chain(self.heap.borrowed.iter()) {
            owner.visit_paths(&mut vec![], &mut |path, node| {
                if let Some(elements) = &node.elements {
                    if elements.precise {
                        roles.push((
                            (name.clone(), path.clone()),
                            elements.states.values().copied().collect::<Vec<_>>(),
                        ));
                    }
                }
            });
        }
        let mut candidates = Vec::new();
        let mut charges = Vec::new();
        for (location, states) in roles {
            let mut current = super::contracts::literal(span, 0);
            let mut entry = current.clone();
            for id in states {
                let bytes = self.growth.elements[id].bytes.clone();
                let snapshot = self.loop_snapshot(span, &bytes);
                if let Some(upper) = self.growth.elements[id].entry_upper() {
                    let mut stable = true;
                    let _ = crate::ast_visitor::expr_visitor_check(&upper, &mut |_, expr| {
                        if let crate::ast::ExprX::Var(name) = &expr.x {
                            stable &= self.stable_scalars.contains(name);
                        }
                        Ok::<(), VirErr>(())
                    });
                    if stable {
                        candidates.push(crate::ast_util::mk_ineq(
                            span,
                            &snapshot,
                            &upper,
                            crate::ast::InequalityOp::Le,
                        ));
                    }
                }
                current = super::contracts::add(span, current, bytes);
                entry = super::contracts::add(span, entry, snapshot);
            }
            charges.push(super::transfer::checked::LoopCharge { location, current, entry });
        }
        self.transitions.loop_charges.insert(span.id, charges);
        candidates
    }

    /// A loop carries original ownership by persistent destination, not by an
    /// ever-growing set of per-iteration element identities.
    pub(super) fn join_input(
        &mut self,
        span: &Span,
        location: &super::paths::LocalPath,
        child: &mut Owner,
    ) -> Result<Option<super::transfer::checked::InputJoin>, VirErr> {
        if self.growth.loop_depth == 0 || child.inputs().is_empty() {
            return Ok(None);
        }
        self.heap.check_partition(&location.0, span)?;
        let mut children = std::collections::BTreeMap::new();
        let mut opaque = false;
        child.visit_paths(&mut vec![], &mut |path, node| {
            if let Some(input) = node.input {
                children.insert(path.clone(), input);
            }
            opaque |= node.elements.as_ref().is_some_and(|elements| !elements.inputs.is_empty());
        });
        if opaque || super::paths::indexed(&location.1) {
            return Err(super::model::unsupported(
                span,
                "a loop transfer without structural input regions",
            ));
        }
        let result = self.transitions.fresh_region();
        let parent = self.heap.root_mut(&location.0).unwrap().at_mut(&location.1).unwrap();
        let previous = parent.input.replace(result);
        parent.view = super::metadata::View::Local;
        parent.elements.as_mut().unwrap().view = super::metadata::View::Local;
        for id in previous.iter().chain(children.values()) {
            self.storage.release_input(*id);
        }
        self.storage.add_input(result);
        fn clear(owner: &mut Owner) {
            owner.input = None;
            for child in owner.children.values_mut() {
                clear(child);
            }
        }
        clear(child);
        Ok(Some(super::transfer::checked::InputJoin { previous, children, result }))
    }

    pub(super) fn loop_inputs(
        &self,
    ) -> std::collections::BTreeMap<super::paths::LocalPath, Option<usize>> {
        let mut inputs = std::collections::BTreeMap::new();
        for (name, owner) in &self.heap.owners {
            owner.visit_paths(&mut vec![], &mut |path, node| {
                inputs.insert((name.clone(), path.clone()), node.input);
            });
        }
        inputs
    }

    /// Earlier profiles describe the first iteration. Original allocations can
    /// only move or be released, so their total at each later iteration's point
    /// cannot increase. Local charges remain checked by inductive loop proofs.
    /// Exit identities, unlike those peak witnesses, denote the completed loop.
    pub(super) fn finish_loop_inputs(
        &mut self,
        span: &Span,
        entry: std::collections::BTreeMap<super::paths::LocalPath, Option<usize>>,
    ) -> Result<(), VirErr> {
        let mut regions = Vec::new();
        for (location, entry) in entry {
            let node = self
                .heap
                .root_mut(&location.0)
                .and_then(|root| root.at_mut(&location.1))
                .ok_or_else(|| {
                    super::model::unsupported(
                        span,
                        "changing fixed ownership roles across loop iterations",
                    )
                })?;
            if node.elements.as_ref().is_some_and(|elements| !elements.inputs.is_empty()) {
                return Err(super::model::unsupported(
                    span,
                    "loop-carried ownership without structural input regions",
                ));
            }
            if node.input != entry {
                let input = node.input.ok_or_else(|| {
                    super::model::unsupported(span, "losing a persistent loop input role")
                })?;
                let exit = self.transitions.fresh_region();
                self.storage.release_input(input);
                self.storage.add_input(exit);
                node.input = Some(exit);
                regions.push(super::transfer::checked::LoopRegion { location, entry, exit });
            }
        }
        self.transitions.loops.insert(span.id, regions);
        Ok(())
    }

    /// Extraction splits a receiver's region into surviving and selected owners.
    /// Replacement passes no selected owner: the destination's original subtree
    /// is released, while the new child keeps its own allocation charges.
    pub(super) fn split_input(
        &mut self,
        span: &Span,
        location: &super::paths::LocalPath,
        child: Option<&mut Owner>,
    ) -> Result<Option<InputSplit>, VirErr> {
        let (name, path) = location;
        let root = self.heap.root(name).expect("tracked ownership destination");
        // Replacing a fixed input node releases its identity through the ordinary
        // owner drop. Only a containing runtime region needs a new remainder.
        let ancestors = path.len() + usize::from(child.is_some());
        let ancestor = (0..ancestors).rev().find_map(|depth| {
            let owner = root.at(&path[..depth])?;
            // Fixed child regions are independent of this node's identity.
            // A fresh replacement beneath one must not split the ancestor.
            if depth < path.len() && !matches!(path[depth], super::heap::OwnerSlot::Element(_)) {
                return None;
            }
            owner.input.map(|input| (depth, input))
        });
        let Some((depth, source)) = ancestor else {
            return Ok(None);
        };
        self.heap.check_partition(name, span)?;
        let remaining = self.transitions.fresh_region();
        self.storage.release_input(source);
        self.storage.add_input(remaining);
        self.heap.root_mut(name).unwrap().at_mut(&path[..depth]).unwrap().input = Some(remaining);
        let mut selected = std::collections::BTreeMap::new();
        fn mark(analysis: &mut Analysis<'_>, owner: &mut Owner) {
            let input = analysis.transitions.fresh_region();
            analysis.storage.add_input(input);
            owner.input = Some(input);
            for child in owner.children.values_mut() {
                mark(analysis, child);
            }
        }
        if let Some(child) = child {
            mark(self, child);
            child.visit_paths(&mut vec![], &mut |path, owner| {
                selected.insert(path.clone(), owner.input.unwrap());
            });
        }
        Ok(Some(InputSplit { source, depth, remaining, selected }))
    }
}
