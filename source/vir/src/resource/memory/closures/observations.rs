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
    /// Verified receiver projections frozen from the actual source binding.
    pub(super) protocol: Option<super::super::synchronization::holders::Captured>,
    /// Native scalar frozen at construction, including mutable parent bindings.
    /// Aggregate scalars need separately checked projections before use.
    pub(super) scalar: Option<Expr>,
    /// Scalar fields of an inline aggregate, observed before the capture moves.
    /// Paths never cross shared pointers or mutable references.
    pub(super) projections: Vec<(Vec<Ident>, Expr)>,
    /// A captured closure keeps its own earlier construction epoch.
    pub(super) environment: Option<EnvironmentId>,
}

#[derive(Clone)]
struct Environment {
    definition: usize,
    /// Static construction and its required loop-occurrence binders. A single
    /// snapshot cannot instantiate these across retained dynamic visits.
    construction: crate::messages::AstId,
    loops: Vec<crate::messages::AstId>,
    fields: Vec<Field>,
    /// A source loop can overwrite the same ghost snapshots on its next visit.
    /// Until lifted through checked occurrence substitutions, this describes
    /// only a representative visit and cannot supply retained worker inputs.
    repeated: bool,
    /// Checked runtime visit coordinates, present only on an instantiated view.
    occurrence: Option<Vec<(crate::messages::AstId, Expr)>>,
}

/// Descriptors survive moves and branch snapshots without creating storage.
/// Missing observations must reject a worker input, never reread its parent.
#[derive(Default)]
pub(in super::super) struct Environments {
    records: BTreeMap<EnvironmentId, Environment>,
}

impl Environments {
    pub(in super::super) fn protocol(
        &self,
        id: EnvironmentId,
        field: usize,
    ) -> Option<super::super::synchronization::holders::Captured> {
        self.records.get(&id)?.fields.get(field)?.protocol
    }

    pub(in super::super) fn projections(
        &self,
        id: EnvironmentId,
        field: usize,
    ) -> &[(Vec<Ident>, Expr)] {
        self.records
            .get(&id)
            .filter(|environment| !environment.repeated)
            .and_then(|environment| environment.fields.get(field))
            .map_or(&[], |field| field.projections.as_slice())
    }

    pub(in super::super) fn nested(
        &self,
        id: EnvironmentId,
        field: usize,
    ) -> Option<EnvironmentId> {
        self.records
            .get(&id)
            .filter(|environment| !environment.repeated)?
            .fields
            .get(field)?
            .environment
    }
    pub(super) fn insert(
        &mut self,
        definition: usize,
        fields: Vec<Field>,
        repeated: bool,
        construction: crate::messages::AstId,
        loops: Vec<crate::messages::AstId>,
    ) -> EnvironmentId {
        let repeated = repeated
            || fields.iter().any(|field| {
                field.environment.is_some_and(|id| {
                    self.records.get(&id).is_none_or(|environment| environment.repeated)
                })
            });
        let id = EnvironmentId(super::super::accounting::Accounting::fresh_allocation());
        self.records.insert(
            id,
            Environment { definition, fields, repeated, construction, loops, occurrence: None },
        );
        id
    }

    pub(in super::super) fn constructed_at(
        &self,
        id: EnvironmentId,
        site: crate::messages::AstId,
    ) -> bool {
        self.records.get(&id).is_some_and(|environment| {
            environment.construction == site
                && (environment.loops.is_empty() || environment.occurrence.is_some())
                && !environment.repeated
        })
    }

    /// Bind the current construction visit before entering its body. The
    /// original repeated descriptor remains unusable without these coordinates.
    /// An environment escaping its construction loops needs a retained descriptor
    /// substitution; the caller cannot reread a later iteration's snapshots.
    pub(in super::super) fn bind_occurrence(
        &mut self,
        id: EnvironmentId,
        active: &[(crate::messages::AstId, Expr)],
        span: &Span,
    ) -> Result<EnvironmentId, VirErr> {
        let mut environment = self
            .records
            .get(&id)
            .cloned()
            .ok_or_else(|| unsupported(span, "worker occurrence without its construction"))?;
        if !environment.repeated {
            return Ok(id);
        }
        if environment.loops.is_empty()
            || !active.iter().map(|(id, _)| *id).collect::<Vec<_>>().starts_with(&environment.loops)
        {
            return Err(unsupported(
                span,
                "stale repeated capture observations outside their construction occurrence",
            ));
        }
        for field in &mut environment.fields {
            if let Some(nested) = field.environment {
                field.environment = Some(self.bind_occurrence(nested, active, span)?);
            }
        }
        environment.repeated = false;
        environment.occurrence = Some(active.to_vec());
        let bound = EnvironmentId(super::super::accounting::Accounting::fresh_allocation());
        self.records.insert(bound, environment);
        Ok(bound)
    }

    /// Only direct native scalars may currently supply scalar substitutions.
    /// This supplies no observation of mutable storage behind a shared handle.
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
    /// Preserve fixed aggregate scalar inputs without treating an owning handle
    /// as an observation of its separately allocated, potentially mutable data.
    pub(in super::super) fn observe_capture_projections(
        &mut self,
        place: &Place,
        span: &Span,
    ) -> Result<Vec<(Vec<Ident>, Expr)>, VirErr> {
        fn visit(
            analysis: &mut Analysis<'_>,
            place: &Place,
            path: &mut Vec<Ident>,
            span: &Span,
            observed: &mut Vec<(Vec<Ident>, Expr)>,
        ) -> Result<(), VirErr> {
            if !path.is_empty() && contracts::scalar(&place.typ) {
                observed.push((
                    path.clone(),
                    analysis.observe_capture_scalar(place, &place.typ, span)?.unwrap(),
                ));
            } else if let TypX::Datatype(datatype, _, _) = &*place.typ {
                // Only already supported one-variant layouts have fixed fields.
                let Ok(variant) = analysis.layouts.struct_variant(&place.typ, span) else {
                    return Ok(());
                };
                let variant = variant.clone();
                for field in variant.fields.iter().filter(|field| field.a.1 == Mode::Exec) {
                    let projection = SpannedTyped::new(
                        span,
                        &field.a.0,
                        PlaceX::Field(
                            FieldOpr {
                                datatype: datatype.clone(),
                                variant: variant.name.clone(),
                                field: field.name.clone(),
                                get_variant: false,
                                check: VariantCheck::None,
                            },
                            place.clone(),
                        ),
                    );
                    path.push(field.name.clone());
                    visit(analysis, &projection, path, span, observed)?;
                    path.pop();
                }
            }
            Ok(())
        }
        let mut observed = vec![];
        visit(self, place, &mut vec![], span, &mut observed)?;
        Ok(observed)
    }

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
