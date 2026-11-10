//! Ownership transitions accepted by body analysis.
//!
//! The symbolic evaluator consumes these records; it cannot rediscover an
//! allocation, move, or mutation from an unchecked source call. Layout sizes,
//! child slots, and resolved owner paths come from the accounting operation.
//! Records describe executable effects, excluding erased proof-state updates.

use crate::ast::*;
use crate::messages::Span;
use crate::resource::memory::heap::{OwnerPath, OwnerSlot};
use std::collections::{HashMap, HashSet};

/// An owner place resolved by the operation that checks its lifetime and layout.
#[derive(Clone)]
pub(in super::super) struct Place {
    /// Source used only to specialize runtime index expressions.
    pub(in super::super) source: Expr,
    /// Checked owner type, including implicit box dereferences.
    pub(in super::super) typ: Typ,
    /// Named owner and its structural path.
    pub(in super::super) location: (VarIdent, OwnerPath),
}

/// One executable ownership rule, with layout decisions supplied by accounting.
#[derive(Clone)]
pub(in super::super) enum Operation {
    /// Allocate a buffer using the checked capacity and inline element size.
    Vector { capacity: Expr, element: u64 },
    /// Allocate a fixed payload; an owning payload is nested under Contents.
    Box { payload: Expr, bytes: u64 },
    /// Initialize checked child slots. The tag distinguishes optional payloads.
    Aggregate { fields: Vec<(Expr, Option<OwnerSlot>)>, tag: u64 },
    /// Append one value, retaining its complete forest beneath the next index.
    Push {
        receiver: Place,
        child: Expr,
        element: u64,
        /// False when entry reservations or section protection require spare room.
        grow: bool,
    },
    /// Extract and reindex; an absent index denotes an optional last element.
    Remove { receiver: Place, index: Option<Expr> },
    /// Read cardinality from the checked receiver.
    Length { receiver: Place },
    /// Replace vector backing with length-sized slice backing.
    IntoSlice { source: Expr, element: u64 },
    /// Consume an optional owner and transfer its Contents child.
    Unwrap { source: Expr },
    /// Consume the owner selected by the recorded operand move.
    Drop { source: Expr },
    /// Inspect the presence tag without consuming its owner.
    Predicate { receiver: Place, present: bool },
    /// Evaluate scalar constructor operands without producing ownership.
    Evaluate { args: Exprs },
    /// Apply an already checked helper, including its resolved borrowed places.
    Call { target: Fun, args: Exprs, borrowed: HashMap<usize, Place> },
}

/// Pattern ownership decisions made while checking the actual match arm.
#[derive(Clone)]
pub(in super::super) enum Pattern {
    Discard,
    Bind(VarIdent),
    Absent,
    Present { payload: Typ, pattern: crate::ast::Pattern },
}

/// Categories keep a place's move distinct from a surrounding operation at
/// the same source span. Coverage is checked before a template can be exported.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Kind {
    Operation,
    Move,
    Assign,
    Pattern,
    Scope,
}

#[derive(Default)]
pub(in super::super) struct Checked {
    /// Semantic operations selected by body accounting.
    pub(super) operations: HashMap<u64, Operation>,
    /// Consumed places, with the actual selected type rather than the outer place type.
    pub(super) moves: HashMap<u64, Place>,
    /// Destinations whose old forests are replaced after RHS evaluation.
    pub(super) assignments: HashMap<u64, Place>,
    /// Checked by-value pattern transfers.
    pub(super) patterns: HashMap<u64, Pattern>,
    /// Owning locals released at each scope exit, if they have not been moved.
    pub(super) scopes: HashMap<u64, Vec<VarIdent>>,
}

impl Checked {
    pub(in super::super) fn operation(&mut self, span: &Span, operation: Operation) {
        self.operations.insert(span.id, operation);
    }

    pub(in super::super) fn movement(&mut self, span: &Span, place: Place) {
        self.moves.insert(span.id, place);
    }

    pub(in super::super) fn assignment(&mut self, span: &Span, place: Place) {
        self.assignments.insert(span.id, place);
    }

    pub(in super::super) fn pattern(&mut self, span: &Span, pattern: Pattern) {
        self.patterns.insert(span.id, pattern);
    }

    pub(in super::super) fn scope(&mut self, span: &Span, locals: Vec<VarIdent>) {
        self.scopes.insert(span.id, locals);
    }

    pub(super) fn covered(&self, used: &HashSet<(Kind, u64)>) -> bool {
        self.operations.keys().all(|id| used.contains(&(Kind::Operation, *id)))
            && self.moves.keys().all(|id| used.contains(&(Kind::Move, *id)))
            && self.assignments.keys().all(|id| used.contains(&(Kind::Assign, *id)))
            && self.patterns.keys().all(|id| used.contains(&(Kind::Pattern, *id)))
            && self.scopes.keys().all(|id| used.contains(&(Kind::Scope, *id)))
    }
}
