//! Conservative lifetime dependencies for extraction from opaque call summaries.
//!
//! Exact element forests transfer charges. An opaque extraction instead copies
//! the enclosing byte upper bound and preserves incoming provenance. Copies have
//! independent accounting identities; ending one never releases another copy.

use super::{
    allocations::{Capture, ReturnedOwner},
    analysis::Analysis,
    contracts,
    footprint::MemoryKind,
    heap::{Owner, OwnerPath, OwnerSlot},
    model::unsupported,
};
use crate::ast::*;
use crate::messages::Span;
use std::collections::{HashMap, HashSet};

pub(super) type CallSources = HashMap<Capture, (Expr, HashSet<Capture>)>;

impl ReturnedOwner {
    pub(super) fn capture_sources(&self, result: &mut HashSet<Capture>) {
        match self {
            Self::Captured { sources, owner } => {
                result.extend(sources.iter().cloned());
                owner.capture_sources(result);
            }
            Self::Input { children, addition, .. } => {
                for child in children.values() {
                    child.capture_sources(result);
                }
                if let Some(elements) = addition {
                    result.extend(elements.captures.iter().cloned());
                }
            }
            Self::Node { children, elements, .. } => {
                for child in children.values() {
                    child.capture_sources(result);
                }
                if let Some(elements) = elements {
                    result.extend(elements.captures.iter().cloned());
                }
            }
            Self::Replaced { elements, .. } => {
                if let Some(elements) = elements {
                    result.extend(elements.captures.iter().cloned());
                }
            }
        }
    }
}

impl Analysis<'_> {
    pub(super) fn capture_dependencies(
        &mut self,
        name: &VarIdent,
        path: &OwnerPath,
        owner: &Owner,
    ) -> HashSet<Capture> {
        let mut sources: HashSet<_> =
            owner.owned_inputs().into_iter().map(Capture::Owned).collect();
        owner.visit(&mut |node| {
            sources.extend(node.captures.iter().cloned());
            if let Some(elements) = &node.elements {
                sources.extend(elements.captures.iter().cloned());
            }
        });
        if self.heap.borrowed.contains_key(name) {
            // Runtime paths are operation-local. The enclosing fixed subtree is
            // a stable, conservative dependency that can cross a call boundary.
            let fixed = path
                .iter()
                .take_while(|slot| !matches!(slot, OwnerSlot::Element(_)))
                .cloned()
                .collect();
            sources.insert(Capture::Borrowed((self.parameters[name], fixed)));
        }
        self.pinned_inputs.extend(sources.iter().filter_map(|source| match source {
            Capture::Owned(index) => Some(*index),
            Capture::Borrowed(_) => None,
        }));
        sources
    }

    pub(super) fn capture_amount(&self, span: &Span, owner: &Owner) -> Expr {
        self.owner_charges(span, owner)
            .into_values()
            .fold(contracts::literal(span, 0), |sum, amount| contracts::add(span, sum, amount))
    }

    /// A fixed child may outlive its parent after a partial move. Give every
    /// structural node its own conservative dependency, including runtime sums.
    pub(super) fn capture_tree(
        &mut self,
        span: &Span,
        owner: &mut Owner,
        amount: Expr,
        sources: &HashSet<Capture>,
    ) {
        self.add_capture_charge(span, owner, amount.clone(), sources.clone(), false);
        for child in owner.children.values_mut() {
            self.capture_tree(span, child, amount.clone(), sources);
        }
    }

    pub(super) fn add_capture_charge(
        &mut self,
        span: &Span,
        owner: &mut Owner,
        amount: Expr,
        sources: HashSet<Capture>,
        after: bool,
    ) {
        owner.captures.extend(sources);
        if contracts::constant(&amount) == Some(0) {
            return;
        }
        if let Some(id) = owner.vector {
            let state = &mut self.growth.vectors[id];
            let assignment = super::symbolic::assign(
                span,
                &state.backing.bytes,
                contracts::add(span, state.backing.bytes.clone(), amount.clone()),
            );
            state.backing.initial_bytes =
                contracts::add(span, state.backing.initial_bytes.clone(), amount.clone());
            if after {
                self.growth.after.entry(span.id).or_default().push(assignment);
            } else {
                self.growth.before.entry(span.id).or_default().push(assignment);
            }
        } else {
            let old = owner
                .dynamic
                .map(|id| self.storage.dynamic_cost(span, id))
                .unwrap_or_else(|| contracts::literal(span, 0));
            let id = owner.dynamic.unwrap_or_else(super::accounting::Accounting::fresh_allocation);
            self.storage.set_allocation(
                id,
                MemoryKind::host_heap(),
                contracts::add(span, old, amount.clone()),
            );
            owner.dynamic = Some(id);
        }
        owner.extent = Some(contracts::add(
            span,
            owner.extent.clone().unwrap_or_else(|| contracts::literal(span, 0)),
            amount.clone(),
        ));
        if let Some(elements) = &mut owner.elements {
            elements.precise = false;
            for id in elements.states.values() {
                self.growth.capture_elements(span, *id, amount.clone(), after);
            }
        }
    }

    /// Resolve dependencies before arguments move or borrowed effects commit.
    pub(super) fn prepare_capture_call(
        &mut self,
        expr: &Expr,
        callee: &Function,
        args: &Exprs,
    ) -> Result<(), VirErr> {
        let summary = &self.summaries[&callee.x.name];
        let mut sources = HashSet::new();
        if let Some(owner) = &summary.allocations.returned {
            owner.capture_sources(&mut sources);
        }
        for child in summary.allocations.children.values() {
            child.owner.capture_sources(&mut sources);
        }
        for elements in summary.allocations.collections.values() {
            sources.extend(elements.captures.iter().cloned());
        }
        if !sources.is_empty() {
            for argument in args.iter() {
                self.check_projection_effects(argument)?;
            }
        }
        let mut values = HashMap::new();
        for source in sources {
            let (parameter, child) = match &source {
                Capture::Owned(index) => summary.input_paths[*index].clone(),
                Capture::Borrowed(path) => path.clone(),
            };
            let (name, mut path) =
                super::paths::expr(&args[parameter], &callee.x.params[parameter].x.typ)
                    .ok_or_else(|| {
                        unsupported(&expr.span, "an opaque capture outside a tracked owner")
                    })?;
            path.extend(child);
            let owner =
                self.heap.root(&name).and_then(|owner| owner.at(&path)).cloned().ok_or_else(
                    || unsupported(&expr.span, "an opaque capture without a live source"),
                )?;
            let dependencies = self.capture_dependencies(&name, &path, &owner);
            let amount = self.capture_amount(&expr.span, &owner);
            let amount = self.allocation_snapshot(&expr.span, amount);
            values.insert(source, (amount, dependencies));
        }
        self.capture_calls.insert(expr.span.id, values);
        Ok(())
    }

    pub(super) fn captured_sources(
        &self,
        span: &Span,
        sources: &HashSet<Capture>,
    ) -> (Expr, HashSet<Capture>) {
        let mut amount = contracts::literal(span, 0);
        let mut dependencies = HashSet::new();
        for source in sources {
            let (bytes, origins) = &self.capture_calls[&span.id][source];
            amount = contracts::add(span, amount, bytes.clone());
            dependencies.extend(origins.iter().cloned());
        }
        (amount, dependencies)
    }

    pub(super) fn check_committed_memory(&mut self, span: &Span) {
        let cost = self
            .storage
            .live_expression(span)
            .map(span, &|amount| Ok::<_, VirErr>(self.growth.after_value(span, amount)))
            .unwrap();
        self.storage.call_cost(span, cost, &HashSet::new(), &HashSet::new(), true);
    }
}
