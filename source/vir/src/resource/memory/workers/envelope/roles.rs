//! Conditions on a product of independently executing worker phases.
use super::*;
use crate::resource::memory::synchronization::holders::{Issuer, PopulationRole};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Class {
    Mutex(Instance),
    Protocol(usize),
}

/// Each count is the number of distinct actors charged to this class.
pub(super) type Held = BTreeMap<Class, u64>;

#[derive(Default)]
pub(super) struct Constraints(Vec<(PopulationRole, Option<Expr>)>);

impl Constraints {
    /// Intern only roles equivalent at their actual types and issuer.
    pub(super) fn register(
        &mut self,
        analysis: &Analysis<'_>,
        params: &HashSet<VarIdent>,
        span: &Span,
        role: PopulationRole,
    ) -> Class {
        if let Some(i) = self.0.iter().position(|(other, _)| *other == role) {
            return Class::Protocol(i);
        }
        // Only a single construction in the coordinator supplies an expression
        // here. Its actual argument must still denote an immutable scalar input.
        let from_constructor = (|| {
            let Issuer::Shared(root) = role.issued.instance else { return None };
            let value = analysis.transitions.fixed_shared_payload(root)?;
            let ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, fun, ..), args, ..
            } = &value.x
            else {
                return None;
            };
            let index = analysis.layouts.capacity_parameters.get(fun)?;
            contracts::quantity(args.get(*index)?, params).ok()
        })();
        let limit = role.limit(span, from_constructor);
        let id = self.0.len();
        self.0.push((role, limit));
        Class::Protocol(id)
    }

    pub(super) fn excludes(&self, a: Class, b: Class) -> bool {
        match (a, b) {
            (Class::Mutex(a), Class::Mutex(b)) => a == b,
            (Class::Protocol(a), Class::Protocol(b)) => self.0[a].0.excludes(&self.0[b].0),
            _ => false,
        }
    }

    pub(super) fn limit(&self, span: &Span, class: Class) -> Option<Expr> {
        if self.excludes(class, class) {
            return Some(contracts::literal(span, 1));
        }
        let Class::Protocol(index) = class else { return None };
        self.0[index].1.clone()
    }

    pub(super) fn combine(
        &self,
        span: &Span,
        left: &Held,
        right: &Held,
        remaining: &BTreeSet<Class>,
    ) -> Option<(Held, Vec<Expr>)> {
        if left.keys().any(|a| right.keys().any(|b| self.excludes(*a, *b))) {
            return None;
        }
        let mut held = left.clone();
        for (&class, &count) in right {
            *held.entry(class).or_default() += count;
        }
        let mut conditions = Vec::new();
        for (&class, &count) in &held {
            if let Some(limit) = self.limit(span, class) {
                if let Some(k) = contracts::constant(&limit) {
                    if count > k {
                        return None;
                    }
                } else if !remaining.contains(&class) {
                    conditions.push(crate::ast_util::mk_ineq(
                        span,
                        &contracts::literal(span, count),
                        &limit,
                        InequalityOp::Le,
                    ));
                }
            }
        }
        // Keep identities needed by future actors, including a different,
        // incompatible reader/writer role on the same issuer.
        held.retain(|a, _| {
            remaining.contains(a) || remaining.iter().any(|b| self.excludes(*a, *b))
        });
        Some((held, conditions))
    }
}

impl Analysis<'_> {
    /// Protocol helpers already have a checked call profile, including their
    /// full allowance and any unrestricted wait. Their bodies must be available.
    pub(super) fn protocol_helper(&self, target: &Fun) -> bool {
        self.summaries.get(target).is_some_and(|s| s.effects.is_some())
            && self.functions.get(target).is_some_and(|f| {
                self.layouts.inline_protocol_value(&f.x.outer_ret.x.typ)
                    || f.x.params.iter().any(|p| self.layouts.inline_protocol_value(&p.x.typ))
            })
    }
}
