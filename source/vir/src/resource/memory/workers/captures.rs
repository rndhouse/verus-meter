//! Source captures and compiler body places are views of the same environment
//! fields. The environment owns their inline storage once. These mappings do
//! not create extra handles, slots, allocations or synchronization instances.
//! Distinct fields may carry aliases of the same canonical target.

use super::super::{
    concurrency::Closure,
    heap::OwnerSlot,
    layout::Layouts,
    model::unsupported,
    paths::{self, LocalPath},
    synchronization::flow,
};
use crate::{ast::*, messages::Span};

/// A runtime field has both source and function-local compiler coordinates.
/// Body places belong to the original closure body, not its FnOnce adapter;
/// composing that adapter requires its actual move/borrow and call edges.
#[derive(Clone)]
struct CaptureView {
    /// Exact original binding and fixed path selected by runtime capture analysis.
    source: LocalPath,
    /// Location in this body's compiler environment, including any self borrow.
    body: flow::Place,
    /// Field in the canonical runtime environment's owner tree.
    slot: OwnerSlot,
    /// Runtime field type. Owned descendants remain beneath this field's slot.
    typ: Typ,
}

/// Disjoint views into one worker's retained capture environment.
#[derive(Clone)]
pub(super) struct Captures {
    fields: Vec<CaptureView>,
}

impl Captures {
    pub(super) fn new(closure: &Closure, layouts: &Layouts, span: &Span) -> Result<Self, VirErr> {
        let mut fields: Vec<CaptureView> = Vec::new();
        for (index, capture) in closure.captures.iter().enumerate() {
            let place = layouts.capture_place(capture, span)?;
            let source = paths::place(&place, &capture.typ).ok_or_else(|| {
                unsupported(span, "a worker capture without an exact source ownership path")
            })?;
            let body = capture.body_place.as_ref().ok_or_else(|| {
                unsupported(span, "a worker capture without a compiler body projection")
            })?;
            for field in &fields {
                let source_overlap = field.source.0 == source.0
                    && (field.source.1.starts_with(&source.1)
                        || source.1.starts_with(&field.source.1));
                let body_overlap = field.body.local == body.local
                    && (field.body.projection.starts_with(&body.projection)
                        || body.projection.starts_with(&field.body.projection));
                if source_overlap || body_overlap {
                    return Err(unsupported(span, "overlapping executable worker capture views"));
                }
            }
            fields.push(CaptureView {
                source,
                body: body.clone(),
                slot: OwnerSlot::Capture(index),
                typ: capture.typ.clone(),
            });
        }
        Ok(Self { fields })
    }

    pub(super) fn owned_slots(&self, layouts: &Layouts) -> std::collections::BTreeSet<OwnerSlot> {
        self.fields
            .iter()
            .filter(|field| layouts.owner(&field.typ))
            .map(|field| field.slot.clone())
            .collect()
    }

    /// Translate a checked source location into the environment owner tree.
    /// Unresolved locations must not fall back to an unrelated parent binding.
    /// This translation alone does not validate a type or prove a live owner.
    pub(super) fn source_path(&self, source: &LocalPath) -> Option<Vec<OwnerSlot>> {
        let field = self
            .fields
            .iter()
            .find(|field| field.source.0 == source.0 && source.1.starts_with(&field.source.1))?;
        Some(
            std::iter::once(field.slot.clone())
                .chain(source.1[field.source.1.len()..].iter().cloned())
                .collect(),
        )
    }

    pub(super) fn compatible(&self, other: &Self) -> bool {
        self.fields.len() == other.fields.len()
            && self.fields.iter().zip(&other.fields).all(|(a, b)| {
                a.source == b.source
                    && a.body == b.body
                    && a.slot == b.slot
                    && crate::ast_util::types_equal(&a.typ, &b.typ)
            })
    }
}
