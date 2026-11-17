//! Capture inputs belong to construction, not to the later spawn operation.
//!
//! These compiler-owned observations describe one checked construction visit.
//! A repeated construction must lift them through its checked occurrence binder;
//! a mutable snapshot variable is never a population of retained environments.

use super::super::{analysis::Analysis, contracts, model::unsupported};
use crate::{ast::*, messages::Span};
use std::collections::BTreeMap;

/// One environment value's immutable descriptor identity. Copying an executable
/// closure copies its capture values, so both copies use the same observations.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(in super::super) struct EnvironmentId(u64);

/// Observations of a field, separate from its inline charge and owned tree.
#[derive(Clone)]
pub(super) struct Field {
    /// Native scalar frozen at construction, including mutable parent bindings.
    /// Aggregate scalars need separately checked projections before use.
    pub(super) scalar: Option<Expr>,
    /// A captured closure keeps its own earlier construction epoch.
    pub(super) environment: Option<EnvironmentId>,
}

struct Environment {
    definition: usize,
    fields: Vec<Field>,
    /// A source loop can overwrite the same ghost snapshots on its next visit.
    /// Until lifted through checked occurrence substitutions, this describes
    /// only a representative visit and cannot supply retained worker inputs.
    repeated: bool,
}

/// Descriptors survive moves and branch snapshots without creating storage.
/// Missing observations must reject a worker input, never reread its parent.
#[derive(Default)]
pub(in super::super) struct Environments {
    records: BTreeMap<EnvironmentId, Environment>,
}

impl Environments {
    pub(super) fn insert(
        &mut self,
        definition: usize,
        fields: Vec<Field>,
        repeated: bool,
    ) -> EnvironmentId {
        let repeated = repeated
            || fields.iter().any(|field| {
                field.environment.is_some_and(|id| {
                    self.records.get(&id).is_none_or(|environment| environment.repeated)
                })
            });
        let id = EnvironmentId(super::super::accounting::Accounting::fresh_allocation());
        self.records.insert(id, Environment { definition, fields, repeated });
        id
    }

    /// Only direct native scalars may currently supply scalar substitutions.
    /// This supplies no observation of mutable storage behind a shared handle.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "worker body inputs consume scalar observations")
    )]
    pub(in super::super) fn scalar(&self, id: EnvironmentId, field: usize) -> Option<&Expr> {
        let environment = self.records.get(&id)?;
        if environment.repeated {
            return None;
        }
        environment.fields.get(field)?.scalar.as_ref()
    }

    pub(in super::super) fn matches(
        &self,
        id: EnvironmentId,
        definition: usize,
        captures: &[super::super::concurrency::Capture],
    ) -> bool {
        self.records.get(&id).is_some_and(|environment| {
            !environment.repeated
                && environment.definition == definition
                && environment.fields.len() == captures.len()
                && environment.fields.iter().zip(captures).all(|(field, capture)| {
                    field.scalar.is_some() == contracts::scalar(&capture.typ)
                        && field.scalar.as_ref().is_none_or(|value| {
                            crate::ast_util::types_equal(&value.typ, &capture.typ)
                        })
                        && match &*capture.typ {
                            TypX::AnonymousClosure(_, _, _, definition) => {
                                field.environment.and_then(|id| self.records.get(&id)).is_some_and(
                                    |nested| !nested.repeated && nested.definition == *definition,
                                )
                            }
                            _ => field.environment.is_none(),
                        }
                })
        })
    }
}

impl Analysis<'_> {
    /// Freeze a direct scalar with an ordinary erased assignment at the actual
    /// construction expression, before it reads/moves any capture. Never infer
    /// a captured value from the parent's current binding at publication.
    pub(in super::super) fn observe_capture_scalar(
        &mut self,
        place: &Place,
        typ: &Typ,
        span: &Span,
    ) -> Result<Option<Expr>, VirErr> {
        if !contracts::scalar(typ) {
            return Ok(None);
        }
        let read = SpannedTyped::new(
            span,
            typ,
            ExprX::ReadPlace(
                place.clone(),
                UnfinalizedReadKind { preliminary_kind: ReadKind::Spec, id: 0 },
            ),
        );
        let source = super::super::projections::spec_value(&read)?;
        let name = VarIdent(
            std::sync::Arc::new("$memory_capture".into()),
            VarIdentDisambiguate::VirTemp(super::super::accounting::Accounting::fresh_allocation()),
        );
        let (value, declaration) = super::super::symbolic::scalar_local(span, name, typ);
        self.growth.declarations.push(declaration);
        self.growth
            .before
            .entry(span.id)
            .or_default()
            .push(super::super::symbolic::assign(span, &value, source));
        Ok(Some(value))
    }

    /// A copy preserves capture inputs as well as creating another inline slot.
    /// Source places outside this checked interface cannot invent observations.
    pub(in super::super) fn copied_environment(
        &self,
        place: &Place,
        typ: &Typ,
    ) -> Result<Option<EnvironmentId>, VirErr> {
        if !matches!(&**typ, TypX::AnonymousClosure(..)) {
            return Ok(None);
        }
        let PlaceX::Local(name) = &place.x else {
            return Err(unsupported(
                &place.span,
                "a closure copy outside a checked environment slot",
            ));
        };
        if !crate::ast_util::types_equal(&place.typ, typ) {
            return Err(unsupported(&place.span, "a closure copy through an unchecked projection"));
        }
        self.slots.get(name).and_then(|value| value.environment).map(Some).ok_or_else(|| {
            unsupported(&place.span, "a closure copy without construction observations")
        })
    }
}
