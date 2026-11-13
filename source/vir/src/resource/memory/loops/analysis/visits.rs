//! Observe completed visits and publish checked scalar and length progress facts.
//!
//! The erased visit ordinal counts back edges independently of counter stride.
//! Progress evidence still produces invariants checked at entry and on back edges.

use super::super::{Loop, local, progress};
use crate::ast::*;
use crate::resource::memory::{
    analysis::Analysis, contracts, heap, metadata, projections, transfer,
};

impl Analysis<'_> {
    /// Count actual back edges independently of the source counter's stride.
    /// These erased updates cannot alter executable storage or overflow behavior.
    pub(super) fn loop_progress(
        &mut self,
        record: &mut Loop,
    ) -> Result<Option<(Expr, Expr)>, VirErr> {
        let Some(control) = &record.control else { return Ok(None) };
        let observe = |value: &Expr| {
            if let Some(transfer::checked::Operation::Length { receiver }) =
                self.transitions.operation_at(&value.span)
            {
                let value = projections::spec_value(&receiver.source).ok()?;
                Some(self.owner_length(
                    &record.span,
                    &heap::Owner {
                        source: Some((receiver.typ.clone(), value)),
                        ..Default::default()
                    },
                ))
            } else {
                projections::spec_value(value).ok()
            }
        };
        let observations = if record.iterator.is_some() {
            (Some(control.start.clone()), Some(control.end.clone()))
        } else {
            (observe(&control.start), observe(&control.end))
        };
        let (Some(left), Some(right)) = observations else {
            return Ok(None);
        };
        let left = SpannedTyped::new(&record.span, &crate::ast_util::int_typ(), left.x.clone());
        let right = SpannedTyped::new(&record.span, &crate::ast_util::int_typ(), right.x.clone());
        // A logical role and the progress condition observe the same entry
        // length. Reuse its snapshot so isolated queries retain that identity.
        let mut snapshot = |source: &Expr, value: &Expr| {
            if let Some(transfer::checked::Operation::Length { receiver }) =
                self.transitions.operation_at(&source.span)
            {
                if let Some(entry) = record.entry_length(&receiver.location) {
                    return entry;
                }
            }
            if let Some(name) = local(source) {
                let current =
                    SpannedTyped::new(&record.span, &crate::ast_util::int_typ(), ExprX::Var(name));
                return self.loop_snapshot(&record.span, &current);
            }
            self.loop_snapshot(&record.span, value)
        };
        let bounds = (snapshot(&control.start, &left), snapshot(&control.end, &right));
        let mut scalars = std::collections::HashMap::new();
        for name in record
            .scalar_steps
            .keys()
            .filter(|name| self.slots.contains_key(*name))
            .cloned()
            .collect::<Vec<_>>()
        {
            let current = SpannedTyped::new(
                &record.span,
                &crate::ast_util::int_typ(),
                ExprX::Var(name.clone()),
            );
            let initial = self.loop_snapshot(&record.span, &current);
            scalars.insert(name, (current, initial));
        }
        let zero = contracts::literal(&record.span, 0);
        let (ordinal, declaration) = metadata::expr::local(
            &record.span,
            "loop_visits",
            crate::ast_util::int_typ(),
            zero.clone(),
            Mode::Spec,
        );
        self.growth.before.entry(record.span.id).or_default().push(declaration);
        self.growth.after.entry(record.body.span.id).or_default().push(metadata::expr::assign(
            &record.body.span,
            &ordinal,
            contracts::add(
                &record.body.span,
                ordinal.clone(),
                contracts::literal(&record.body.span, 1),
            ),
        ));
        record.progress = Some(progress::Observation { ordinal: ordinal.clone(), bounds, scalars });
        Ok(Some((ordinal, zero)))
    }

    /// Publish only validated translations and length changes as ordinary loop
    /// invariants. Each relationship is proved at entry and on every back edge.
    pub(in crate::resource::memory) fn apply_progress_evidence(
        &mut self,
        evidence: &std::collections::HashMap<u64, progress::Evidence>,
    ) {
        for (id, evidence) in evidence {
            let record = self.transitions.loops.get_mut(id).unwrap();
            let Some(observation) = &record.progress else { continue };
            let span = &record.span;
            let ordinal = &observation.ordinal;
            let gap = record.control.as_ref().unwrap().gap(
                evidence.bounds.0.clone().unwrap_or_else(|| observation.bounds.0.clone()),
                evidence.bounds.1.clone().unwrap_or_else(|| observation.bounds.1.clone()),
            );
            let bound = progress::count(span, gap, evidence.stride);
            record.visits_bound = Some(bound.clone());
            if !record.head_breaks.is_empty() {
                // Verus cannot assume the negated while condition after a
                // break. Check the completed count on all real exits instead.
                self.growth
                    .loop_ensures
                    .entry(*id)
                    .or_default()
                    .push(crate::ast_util::mk_eq(span, ordinal, &bound));
            }
            let mut facts = vec![
                crate::ast_util::mk_ineq(
                    span,
                    &contracts::literal(span, 0),
                    ordinal,
                    InequalityOp::Le,
                ),
                crate::ast_util::mk_ineq(span, ordinal, &bound, InequalityOp::Le),
            ];
            for (source, snapshot) in [
                (&record.control.as_ref().unwrap().start, &observation.bounds.0),
                (&record.control.as_ref().unwrap().end, &observation.bounds.1),
            ] {
                if let Some(name) = local(source) {
                    if !record.effects.writes.contains(&name) {
                        let current =
                            SpannedTyped::new(span, &crate::ast_util::int_typ(), ExprX::Var(name));
                        facts.push(crate::ast_util::mk_eq(span, snapshot, &current));
                    }
                }
            }
            for (snapshot, initial) in [
                (&observation.bounds.0, &evidence.bounds.0),
                (&observation.bounds.1, &evidence.bounds.1),
            ] {
                if let Some(initial) = initial {
                    facts.push(crate::ast_util::mk_eq(span, snapshot, initial));
                }
            }
            for (name, initial) in &evidence.scalars {
                if let Some((_, snapshot)) = observation.scalars.get(name) {
                    facts.push(crate::ast_util::mk_eq(span, snapshot, initial));
                }
            }
            for (name, definition) in &evidence.definitions {
                let current = SpannedTyped::new(span, &definition.typ, ExprX::Var(name.clone()));
                facts.push(crate::ast_util::mk_eq(span, &current, definition));
            }
            for (location, initial) in &evidence.entry_lengths {
                if let Some(charge) =
                    record.charges.iter().find(|charge| &charge.location == location)
                {
                    facts.push(crate::ast_util::mk_eq(span, &charge.length.1, initial));
                }
            }
            let translated = |initial: &Expr, step: i128| {
                if step >= 0 {
                    contracts::add(
                        span,
                        initial.clone(),
                        contracts::multiply(
                            span,
                            metadata::expr::integer(span, step),
                            ordinal.clone(),
                        ),
                    )
                } else {
                    contracts::subtract(
                        span,
                        initial.clone(),
                        contracts::multiply(
                            span,
                            metadata::expr::integer(span, -step),
                            ordinal.clone(),
                        ),
                    )
                }
            };
            if let Some(iterator) = &record.iterator {
                facts.push(crate::ast_util::mk_eq(
                    span,
                    &iterator.position,
                    &translated(&observation.bounds.0, 1),
                ));
                facts.push(crate::ast_util::mk_eq(span, &iterator.length, &observation.bounds.1));
            }
            for (name, (current, initial)) in &observation.scalars {
                let (_, step) = &record.scalar_steps[name];
                facts.push(crate::ast_util::mk_eq(span, current, &translated(initial, *step)));
            }
            for (location, step) in &evidence.lengths {
                if let Some(charge) =
                    record.charges.iter().find(|charge| &charge.location == location)
                {
                    let expected = translated(&charge.length.1, *step);
                    let expected = if *step < 0 {
                        contracts::maximum(span, contracts::literal(span, 0), expected)
                    } else {
                        expected
                    };
                    facts.push(crate::ast_util::mk_eq(span, &charge.length.0, &expected));
                }
            }
            for (location, expected) in &evidence.prefixes {
                if let Some(charge) =
                    record.charges.iter().find(|charge| &charge.location == location)
                {
                    facts.push(crate::ast_util::mk_eq(span, &charge.length.0, expected));
                }
            }
            self.growth.loops.entry(*id).or_default().extend(facts);
        }
    }
}
