//! Source-semantic invocation of an owned, zero-argument worker closure.
//!
//! Rust's Fn/FnMut bodies borrow their environment; FnOnce bodies own it.
//! Calling any of these through FnOnce consumes the outer environment. A borrowed
//! body returning therefore leaves an environment to destroy, whereas an owned
//! body's cleanup must already have consumed every capture not moved elsewhere.
//! Neither rule depends on a generated compiler wrapper.
//!
//! The original body graph remains the evidence for explicit moves, drops,
//! branches, early returns and unwind obligations. This boundary description is
//! not a checked body summary and does not prove panic freedom.
//!
//! Rust leaves implicit capture destruction order unspecified. Capture indices
//! identify fields, not a release ordering usable for synchronization precision.
//! See <https://doc.rust-lang.org/reference/destructors.html#destructors.operation>
//! and <https://doc.rust-lang.org/reference/types/closure.html#call-traits-and-coercions>.

use super::{super::model::unsupported, super::synchronization::flow, Closure};
use crate::{ast::ClosureKind, ast::VirErr, messages::Span};

/// Access to the existing environment while the original source body runs.
/// In every case the worker owns the outer environment; no capture is cloned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Invocation {
    /// The body takes ownership; its moves and cleanup must account for captures.
    OwnedBody,
    /// The body borrows the environment immutably. Its return does not drop it.
    SharedBody,
    /// The body borrows the environment mutably. Replaced owners and new owners
    /// require checked body effects; return alone does not destroy the environment.
    MutableBody,
}

impl Invocation {
    /// Check the source-body interface using trusted frontend capture/type facts.
    /// This checks neither the body effects nor its normal/unwind feasibility.
    /// Missing capture projections still reject; removing wrapper matching must
    /// not manufacture the connection between runtime owners and source effects.
    pub fn checked(closure: &Closure, span: &Span) -> Result<Self, VirErr> {
        if closure.body.arguments != 1 || closure.body.locals < 2 {
            return Err(unsupported(span, "a worker invocation with explicit closure arguments"));
        }
        let invocation = match closure.kind {
            ClosureKind::FnOnce => Self::OwnedBody,
            ClosureKind::Fn => Self::SharedBody,
            ClosureKind::FnMut => Self::MutableBody,
        };
        for capture in &closure.captures {
            let Some(place) = &capture.body_place else {
                return Err(unsupported(
                    span,
                    "a worker capture without a compiler body projection",
                ));
            };
            // These are original body coordinates, not generated wrapper locals.
            // The frontend maps post-erasure fields to this receiver; it may map
            // several disjoint runtime fields beneath one lifetime-check field.
            let projection = if invocation == Self::OwnedBody {
                place.projection.as_slice()
            } else {
                let Some((flow::Projection::Deref, rest)) = place.projection.split_first() else {
                    return Err(unsupported(
                        span,
                        "a borrowed worker body without its environment view",
                    ));
                };
                rest
            };
            if place.local != 1 || !matches!(projection.first(), Some(flow::Projection::Field(_))) {
                return Err(unsupported(span, "a worker capture outside its body environment"));
            }
        }
        Ok(invocation)
    }

    /// Whether normal body return still requires destruction of the environment's
    /// remaining captures. Process this group in unspecified order, retaining the
    /// result throughout cleanup. A moved/returned owner is not in this group.
    /// For OwnedBody, check that body effects have already emptied the environment;
    /// applying a second implicit cleanup would hide missing or duplicate effects.
    pub fn cleans_up_after_body(self) -> bool {
        self != Self::OwnedBody
    }
}
