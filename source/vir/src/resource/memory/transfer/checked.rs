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

/// Disjoint lifetime regions created by partitioning an owned input.
#[derive(Clone)]
pub(in super::super) struct InputSplit {
    /// Existing input-region identity, relative to its owning ancestor.
    pub(in super::super) source: usize,
    /// Number of receiver or destination path steps belonging to that ancestor.
    pub(in super::super) depth: usize,
    /// New identity for the ancestor's remaining allocations.
    pub(in super::super) remaining: usize,
    /// New identities for disjoint fixed nodes of the extracted child. Empty
    /// when replacement drops the selected subtree instead of transferring it.
    pub(in super::super) selected: std::collections::BTreeMap<OwnerPath, usize>,
}

/// Original regions transferred into one runtime collection slot.
#[derive(Clone)]
pub(in super::super) struct InputJoin {
    /// Destination's original region before insertion, if it has one.
    pub(in super::super) previous: Option<usize>,
    /// Disjoint original regions of the transferred child's fixed nodes.
    pub(in super::super) children: std::collections::BTreeMap<OwnerPath, usize>,
    /// Joined original region retained by the destination after insertion.
    pub(in super::super) result: usize,
}

/// A persistent input role has one lifetime identity after a checked branch.
#[derive(Clone)]
pub(in super::super) struct InputChoice {
    /// Original allocations surviving the true branch, if any.
    pub(in super::super) yes: Option<usize>,
    /// Original allocations surviving the false branch, if any.
    pub(in super::super) no: Option<usize>,
    /// Conditional region used by all later observations of this role.
    pub(in super::super) result: usize,
}

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

/// Replacement commits after RHS evaluation, preserving displaced/new overlap.
#[derive(Clone)]
pub(in super::super) struct Assignment {
    /// Checked destination whose physical forest receives the replacement.
    pub(in super::super) destination: Place,
    /// Original input region after removing the displaced subtree, if any.
    pub(in super::super) input: Option<InputSplit>,
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
        /// Replacement allocation observed by local accounting before the push.
        allocation: Option<Expr>,
        /// Original input regions joined into the receiver by this insertion.
        input: Option<InputJoin>,
    },
    /// Extract and reindex; an absent index denotes an optional last element.
    Remove { receiver: Place, index: Option<Expr>, input: Option<InputSplit> },
    /// Read cardinality from the checked receiver.
    Length { receiver: Place },
    /// Replace vector backing with length-sized slice backing.
    IntoSlice {
        source: Expr,
        element: u64,
        /// New length-sized allocation observed before releasing old backing.
        allocation: Expr,
    },
    /// Consume an optional owner and transfer its Contents child.
    Unwrap { source: Expr },
    /// Consume the owner selected by the recorded operand move.
    Drop { source: Expr },
    /// Inspect the presence tag without consuming its owner.
    Predicate { receiver: Place, present: bool },
    /// Evaluate scalar constructor operands without producing ownership.
    Evaluate { args: Exprs },
    /// Apply an already checked helper, including its resolved borrowed places.
    Call {
        target: Fun,
        /// Instantiated workspace contract; incoming allocations stay external.
        budget: Expr,
        args: Exprs,
        borrowed: HashMap<usize, Place>,
        modified: std::collections::BTreeSet<usize>,
        /// Incoming regions retired by fixed-child replacement effects. The
        /// callee's peak is accounted before these caller lifetimes end.
        replaced_inputs: Vec<Assignment>,
    },
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
    Branch,
    Move,
    Assign,
    Pattern,
    Scope,
    Loop,
}

#[derive(Default)]
pub(in super::super) struct Checked {
    /// Shared loop structure and boundaries, published after body accounting.
    pub(in super::super) loops: HashMap<u64, crate::resource::memory::loops::Loop>,
    /// Conditional lifetime joins accepted by branch accounting.
    pub(in super::super) branches: HashMap<u64, Vec<InputChoice>>,
    /// Original owned parameter nodes, before any runtime partitioning.
    pub(super) inputs: Vec<crate::resource::memory::paths::InputPath>,
    /// Number of additional, operation-derived input lifetime regions.
    regions: usize,
    /// Ordered writes let operation-local loans distinguish mutation from reads.
    mutations: Vec<(VarIdent, OwnerPath)>,
    /// Semantic operations selected by body accounting.
    pub(super) operations: HashMap<u64, Operation>,
    /// Consumed places, with the actual selected type rather than the outer place type.
    pub(super) moves: HashMap<u64, Place>,
    /// Destinations whose old forests are replaced after RHS evaluation.
    pub(super) assignments: HashMap<u64, Assignment>,
    /// Checked by-value pattern transfers.
    pub(super) patterns: HashMap<u64, Pattern>,
    /// Owning locals released at each scope exit, if they have not been moved.
    pub(super) scopes: HashMap<u64, Vec<VarIdent>>,
}

impl Checked {
    /// Read the semantic operation already accepted by body accounting.
    pub(in super::super) fn operation_at(&self, span: &Span) -> Option<&Operation> {
        self.operations.get(&span.id)
    }

    pub(in super::super) fn input(&mut self, parameter: usize, path: OwnerPath) {
        assert_eq!(self.regions, 0);
        self.inputs.push((parameter, path));
    }

    pub(in super::super) fn fresh_region(&mut self) -> usize {
        let id = self.inputs.len() + self.regions;
        self.regions += 1;
        id
    }

    pub(in super::super) fn operation(&mut self, span: &Span, operation: Operation) {
        match &operation {
            Operation::Push { receiver, .. } | Operation::Remove { receiver, .. } => {
                self.mutations.push(receiver.location.clone());
            }
            Operation::Call { borrowed, modified, .. } => {
                for index in modified {
                    if let Some(place) = borrowed.get(index) {
                        self.mutations.push(place.location.clone());
                    }
                }
            }
            _ => {}
        }
        self.operations.insert(span.id, operation);
    }

    pub(in super::super) fn movement(&mut self, span: &Span, place: Place) {
        self.moves.insert(span.id, place);
    }

    pub(in super::super) fn assignment(
        &mut self,
        span: &Span,
        place: Place,
        input: Option<InputSplit>,
    ) {
        self.mutations.push(place.location.clone());
        self.assignments.insert(span.id, Assignment { destination: place, input });
    }

    pub(in super::super) fn pattern(&mut self, span: &Span, pattern: Pattern) {
        self.patterns.insert(span.id, pattern);
    }

    pub(in super::super) fn scope(&mut self, span: &Span, locals: Vec<VarIdent>) {
        self.scopes.insert(span.id, locals);
    }

    pub(in super::super) fn revision(&self) -> usize {
        self.mutations.len()
    }

    /// A descendant write changes this loan's subtree. Nested projections retain
    /// their source index identities for the duration of the operation.
    pub(in super::super) fn changed_since(
        &self,
        revision: usize,
        place: &(VarIdent, OwnerPath),
    ) -> bool {
        self.mutations[revision..]
            .iter()
            .any(|(name, path)| name == &place.0 && path.starts_with(&place.1))
    }

    pub(super) fn covered(&self, used: &HashSet<(Kind, u64)>) -> bool {
        self.branches.keys().all(|id| used.contains(&(Kind::Branch, *id)))
            && self.operations.keys().all(|id| used.contains(&(Kind::Operation, *id)))
            && self.moves.keys().all(|id| used.contains(&(Kind::Move, *id)))
            && self.assignments.keys().all(|id| used.contains(&(Kind::Assign, *id)))
            && self.patterns.keys().all(|id| used.contains(&(Kind::Pattern, *id)))
            && self.scopes.keys().all(|id| used.contains(&(Kind::Scope, *id)))
            && self.loops.keys().all(|id| used.contains(&(Kind::Loop, *id)))
    }
}
