//! Snapshot collection charges and construct checked conservation candidates.
//!
//! Zero-charge and append-backing facts remain ordinary inductive obligations,
//! independent of the ownership transfer graph that selects conservation groups.

use super::super::{Charge, Loop, Transfer};
use crate::ast::*;
use crate::resource::memory::{analysis::Analysis, contracts};

impl Analysis<'_> {
    /// Preserve zero charge only with an explicit, checked loop invariant.
    /// Potential backing writes also invalidate first-visit zero shortcuts.
    pub(super) fn loop_zero_candidates(
        &mut self,
        record: &Loop,
        facts: &mut Vec<Expr>,
    ) -> std::collections::HashSet<usize> {
        let mut zero = std::collections::HashSet::new();
        for (name, owner) in self.heap.owners.iter().chain(self.heap.borrowed.iter()) {
            owner.visit_paths(&mut vec![], &mut |path, node| {
                let location = (name.clone(), path.clone());
                if let Some(id) = node.vector {
                    self.growth.vectors[id].loop_backing |= record.grows_backing(&location);
                }
                if !record.grows_children(&location) {
                    if let Some(elements) = &node.elements {
                        for id in elements.states.values() {
                            if self.growth.elements[*id].unchanged_zero() {
                                zero.insert(*id);
                                facts.push(crate::ast_util::mk_eq(
                                    &record.span,
                                    &self.growth.elements[*id].bytes,
                                    &contracts::literal(&record.span, 0),
                                ));
                            }
                        }
                    }
                }
            });
        }
        zero
    }

    /// Snapshot potential conservation groups before the body changes counters.
    /// The checked iteration graph chooses groups later; every candidate remains
    /// an ordinary invariant proved at loop entry and on all back edges.
    pub(super) fn loop_charge_candidates(&mut self, record: &mut Loop) -> Vec<Expr> {
        let span = &record.span;
        let mut roles = Vec::new();
        for (name, owner) in self.heap.owners.iter().chain(self.heap.borrowed.iter()) {
            owner.visit_paths(&mut vec![], &mut |path, node| {
                if node.vector.is_some()
                    || node.elements.as_ref().is_some_and(|elements| elements.precise)
                {
                    roles.push((
                        (name.clone(), path.clone()),
                        node.elements
                            .as_ref()
                            .filter(|elements| elements.precise)
                            .map(|elements| elements.states.values().copied().collect::<Vec<_>>())
                            .unwrap_or_default(),
                        node.vector,
                        self.owner_length(span, node),
                    ));
                }
            });
        }
        let mut candidates = Vec::new();
        let mut charges = Vec::new();
        for (location, states, vector, length) in roles {
            let mut current = contracts::literal(span, 0);
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
                current = contracts::add(span, current, bytes);
                entry = contracts::add(span, entry, snapshot);
            }
            let backing = vector.map(|id| {
                let bytes = self.growth.vectors[id].backing.bytes.clone();
                let snapshot = self.loop_snapshot(span, &bytes);
                (bytes, snapshot)
            });
            let length = SpannedTyped::new(span, &crate::ast_util::int_typ(), length.x.clone());
            let snapshot = self.loop_snapshot(span, &length);
            let reservation = vector.map(|id| {
                let state = self.growth.vectors[id].clone();
                (state.capacity.clone(), self.loop_snapshot(span, &state.capacity), state.element)
            });
            charges.push(Charge {
                location,
                current,
                entry,
                backing,
                length: (length, snapshot),
                reservation,
            });
        }
        record.charges = charges;
        candidates
    }
}

impl Loop {
    /// These are proof candidates, not assumptions or inferred byte allowances.
    pub(super) fn conservation(&self, transfers: &[Transfer]) -> Vec<Expr> {
        // Alternative destinations belong to one connected conservation group.
        // Pairwise bounds would incorrectly require each destination to contain
        // everything removed from the source on every branch.
        let mut groups: Vec<std::collections::BTreeSet<usize>> = Vec::new();
        for transfer in transfers {
            let mut group = std::collections::BTreeSet::from([transfer.source, transfer.target]);
            let mut index = 0;
            while index < groups.len() {
                if !groups[index].is_disjoint(&group) {
                    group.extend(groups.remove(index));
                    index = 0;
                } else {
                    index += 1;
                }
            }
            groups.push(group);
        }
        groups.sort();
        let mut candidates = Vec::new();
        for group in groups {
            let sum = |entry: bool| {
                group.iter().fold(contracts::literal(&self.span, 0), |sum, index| {
                    let charge = &self.charges[*index];
                    contracts::add(
                        &self.span,
                        sum,
                        if entry { charge.entry.clone() } else { charge.current.clone() },
                    )
                })
            };
            let mut upper = sum(true);
            let mut additions = std::collections::BTreeMap::new();
            for transfer in transfers.iter().filter(|transfer| group.contains(&transfer.source)) {
                if let Some(additional) = &transfer.additional {
                    additions
                        .entry(transfer.target)
                        .and_modify(|old: &mut Expr| {
                            *old = contracts::maximum(&self.span, old.clone(), additional.clone());
                        })
                        .or_insert_with(|| additional.clone());
                }
            }
            for (target, amount) in additions {
                let charge = &self.charges[target];
                let completed = contracts::subtract(
                    &self.span,
                    charge.length.0.clone(),
                    charge.length.1.clone(),
                );
                upper = contracts::add(
                    &self.span,
                    upper,
                    contracts::multiply(&self.span, amount, completed),
                );
            }
            candidates.push(crate::ast_util::mk_ineq(
                &self.span,
                &sum(false),
                &upper,
                InequalityOp::Le,
            ));
            if group.len() == 1 {
                let role = *group.first().unwrap();
                if transfers
                    .iter()
                    .any(|transfer| transfer.source == role && transfer.target == role)
                {
                    if let Some((bytes, entry)) = &self.charges[role].backing {
                        candidates.push(crate::ast_util::mk_ineq(
                            &self.span,
                            bytes,
                            entry,
                            InequalityOp::Le,
                        ));
                    }
                }
            }
        }
        let targets: std::collections::BTreeSet<_> = transfers
            .iter()
            .filter(|transfer| transfer.additional.is_some() && transfer.source != transfer.target)
            .map(|transfer| transfer.target)
            .collect();
        for target in targets {
            let charge = &self.charges[target];
            candidates.push(crate::ast_util::mk_ineq(
                &self.span,
                &contracts::literal(&self.span, 0),
                &charge.length.1,
                InequalityOp::Le,
            ));
            candidates.extend(charge.append_backing(&self.span));
        }
        candidates
    }
}

impl Charge {
    /// Entry reservation remains available while append-only backing can grow.
    /// Retained root bytes are separate from the appended children's charges.
    pub(super) fn append_backing(&self, span: &crate::messages::Span) -> Vec<Expr> {
        let (Some((bytes, entry)), Some((capacity, initial, element))) =
            (&self.backing, &self.reservation)
        else {
            return Vec::new();
        };
        let replacement = contracts::multiply(
            span,
            contracts::literal(span, *element),
            crate::resource::memory::growth::grown_capacity(span, self.length.0.clone(), *element),
        );
        let upper = crate::resource::memory::growth::select(
            span,
            crate::ast_util::mk_ineq(span, &self.length.0, initial, InequalityOp::Le),
            entry.clone(),
            contracts::maximum(span, entry.clone(), replacement),
        );
        vec![
            crate::ast_util::mk_ineq(span, initial, capacity, InequalityOp::Le),
            crate::ast_util::mk_ineq(span, bytes, &upper, InequalityOp::Le),
        ]
    }
}
