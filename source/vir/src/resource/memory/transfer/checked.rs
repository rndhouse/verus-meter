//! Ownership transitions accepted by body analysis.
//!
//! The symbolic evaluator consumes these records; it cannot rediscover an
//! allocation, move, or mutation from an unchecked source call. Layout sizes,
//! child slots, and resolved owner paths come from the accounting operation.
//! Records describe executable effects, excluding erased proof-state updates.

use crate::ast::*;
use crate::messages::{AstId, Span};
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
    /// Receiver path steps belonging to the persistent region's ancestor.
    pub(in super::super) depth: usize,
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

/// One argument's original region, optionally selected from an enclosing input.
#[derive(Clone)]
pub(in super::super) struct OriginSource {
    /// Original lifetime identity before the call.
    pub(in super::super) input: usize,
    /// Fixed path within the argument at which this disjoint region belongs.
    pub(in super::super) path: OwnerPath,
    /// A loan beneath an enclosing region selects the argument's runtime path.
    pub(in super::super) selection: Option<(Place, usize)>,
}

/// One post-call identity, interpreted using the callee's original-only output.
#[derive(Clone)]
pub(in super::super) struct OriginTarget {
    /// Borrowed output parameter, or the returned owner.
    pub(in super::super) parameter: Option<usize>,
    /// One disjoint fixed node; `None` assembles the complete output forest.
    pub(in super::super) path: Option<OwnerPath>,
    /// An indexed loan writes its updated original forest into this ancestor.
    pub(in super::super) ancestor: Option<OriginSource>,
}

/// Provenance composition is independent of the helper's new allocation charges.
#[derive(Clone, Default)]
pub(in super::super) struct CallOrigins {
    /// Original argument nodes captured before argument evaluation.
    pub(in super::super) sources: std::collections::BTreeMap<usize, Vec<OriginSource>>,
    /// Fresh caller identities computed from the callee's original-only outputs.
    pub(in super::super) targets: std::collections::BTreeMap<usize, OriginTarget>,
    /// Callee intermediate regions need separate caller identities in peak profiles.
    pub(in super::super) peaks: std::collections::BTreeMap<usize, usize>,
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

/// Substitution data derived at an actual spawn, replayed by the ownership trace.
#[derive(Clone)]
pub(in super::super) struct WorkerPublication {
    /// Executable closure operand.
    pub(in super::super) source: Expr,
    /// Family and ordered loop coordinates.
    pub(in super::super) identity: Expr,
    /// Layout of the original captures.
    pub(in super::super) inputs: Vec<(Typ, OwnerSlot)>,
    /// Captured worker-vector observations by input index.
    pub(in super::super) populations: HashMap<usize, Expr>,
    /// Checked result relative to the captures.
    pub(in super::super) result: super::Template,
    /// Constructor whose payload supplies the embedded handle observation.
    pub(in super::super) payload_handle: Option<super::super::shared::RootId>,
}

/// One executable ownership rule, with layout decisions supplied by accounting.
#[derive(Clone)]
pub(in super::super) enum Operation {
    /// A verified writer transfers one whole payload from or to this checked cell slot.
    RwWrite {
        receiver: Expr,
        slot: Place,
        replacement: Option<Expr>,
        /// An imported payload has a checked exclusive acquisition in this worker.
        acquired: Option<(
            super::super::synchronization::local::Interval,
            super::super::workers::SourceVisit<AstId>,
        )>,
    },
    /// A compiler-resolved native dereference borrows this existing acquisition.
    GuardBorrow { source: Expr, interval: super::super::synchronization::local::Interval },
    /// Actual discriminant of the lock Result at a native is_ok/is_err test.
    LockPredicate { receiver: Expr, observed: Expr },
    /// A proved-success Result extraction moves its release responsibility.
    GuardExtract { source: Expr },
    /// The protected root retains its constructor occurrence independently of moves.
    MutexNew {
        payload: Expr,
        slot: Option<OwnerSlot>,
        instance: super::super::synchronization::Instance,
        occurrence: super::super::synchronization::local::Occurrence,
    },
    /// A normal blocking acquisition owns a guard in either Result variant.
    MutexLock {
        receiver: Expr,
        interval: super::super::synchronization::local::Interval,
        occurrence: super::super::synchronization::local::Occurrence,
    },
    /// A finite iterator operation accepted by its layout and operation adapter.
    Iterator(crate::resource::memory::iterators::Operation),
    /// Read the length of a checked shared slice.
    SliceLength { receiver: Expr },
    /// A checked array borrow coerced to a shared slice with a fixed length.
    ArraySlice { source: Expr, length: Expr },
    /// Allocate a buffer using the checked capacity and inline element size.
    Vector {
        capacity: Expr,
        element: u64,
        /// Erased constructor observation used if the source capacity can change.
        snapshot: Option<VarIdent>,
    },
    /// Allocate a fixed payload; an owning payload is nested under Contents.
    Box { payload: Expr, bytes: u64 },
    /// A body-local canonical allocation. Its identity may be used to prove
    /// internal observations but cannot escape as a caller-relative input.
    StrongNew { payload: Expr, root: super::super::shared::RootId, coordinates: Vec<(u64, Expr)> },
    /// A unique strong handle yields the current contents of its checked allocation.
    StrongTake { source: Expr, root: super::super::shared::RootId },
    /// Clone one strong link from a checked borrowed place. The backing stays
    /// in its canonical root and the receiver retains its own handle.
    StrongClone { receiver: Place },
    /// Capture transport happens at construction; it does not execute the body.
    Closure { captures: Vec<(super::super::concurrency::CaptureMode, Place)> },
    /// Publish a checked body with a snapshot of its concrete capture values.
    WorkerPublish(WorkerPublication),
    /// Collect exactly the runtime handle consumed by the source operation.
    WorkerJoin {
        /// Indexed by-value mutex ownership, bound to this actual join.
        mutex_receipt: Option<Box<super::super::workers::MutexReceipt>>,
        /// Freshly received outer allocation whose payload handle comes from the selected record.
        payload_handle: Option<super::super::shared::RootId>,
        source: Expr,
        /// Present only when the join checks the selected result against this fixed root.
        returned_root: Option<super::super::shared::RootId>,
    },
    /// Consume a helper input handle without inferring its completion outcome.
    ParameterJoin {
        source: Expr,
        phases: std::sync::Arc<super::super::workers::states::JoinPhases>,
    },
    /// Initialize checked child slots. The tag distinguishes optional payloads.
    Aggregate { fields: Vec<(Expr, Option<OwnerSlot>)>, tag: u64 },
    /// Append one value, retaining its complete forest beneath the next index.
    Push {
        receiver: Place,
        child: Expr,
        /// Complete shared backing transferred to this directly retained handle.
        carried_shared: Option<Expr>,
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
    /// Consume an optional or joined result and transfer its payload description.
    Unwrap {
        source: Expr,
        /// Every possible checked worker body supplies a scalar description.
        /// Ordinary optional values and unknown worker results have none.
        observed_scalar: bool,
    },
    /// The reachable arm and payload of a match on a checked worker join.
    JoinedMatch {
        source: crate::ast::Place,
        pattern: crate::ast::Pattern,
        body: Expr,
        observed_scalar: bool,
    },
    /// Consume the owner selected by the recorded operand move.
    Drop { source: Expr },
    /// Inspect the presence tag without consuming its owner.
    Predicate { receiver: Place, present: bool },
    /// Evaluate scalar constructor operands without producing ownership.
    Evaluate { args: Exprs },
    /// Apply an already checked helper, including its resolved borrowed places.
    Call {
        target: Fun,
        /// Caller-side return charge identities indexed by the same paths as
        /// the callee's exit alternatives. Moves keep their previous identity.
        returned: Vec<super::super::accounting::ReturnedStorage>,
        synchronization: Option<Box<super::super::synchronization::helpers::Call>>,
        /// Instantiated workspace contract; incoming allocations stay external.
        budget: Expr,
        args: Exprs,
        borrowed: HashMap<usize, Place>,
        modified: std::collections::BTreeSet<usize>,
        /// Incoming regions retired by fixed-child replacement effects. The
        /// callee's peak is accounted before these caller lifetimes end.
        replaced_inputs: Vec<Assignment>,
        /// Checked correspondence between caller and callee lifetime regions.
        origins: CallOrigins,
    },
}

/// Pattern ownership decisions made while checking the actual match arm.
#[derive(Clone)]
pub(in super::super) enum Pattern {
    /// Destructuring binds the value taken from the cell and the separate writer.
    WriterPair,
    /// The source tag chooses an acquiring or non-acquiring arm. An unsplit
    /// try-lock error preserves both possibilities.
    LockOutcome {
        interval: super::super::synchronization::local::Interval,
        acquired: Option<bool>,
    },
    Bind(VarIdent),
    Absent,
    Present {
        payload: Typ,
        pattern: crate::ast::Pattern,
    },
}

/// Categories keep a place's move distinct from a surrounding operation at
/// the same source span. Coverage is checked before a template can be exported.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(in super::super) enum Kind {
    Operation,
    Branch,
    Move,
    Assign,
    Pattern,
    Scope,
    Loop,
    Exit,
}

#[derive(Default)]
pub(in super::super) struct Checked {
    /// Shared contents observed under a specific worker acquisition. A later
    /// acquisition has a new input even if it addresses the same root.
    pub(in super::super) protected_versions: super::super::synchronization::versions::Versions,
    /// Fixed-root histories connect body-local inputs to the source release
    /// and incoming allocation forest that produced each predecessor.
    pub(in super::super) protected_histories: std::collections::BTreeMap<
        super::super::shared::RootId,
        super::super::synchronization::versions::History,
    >,
    /// Charged result paths on each reaching normal exit, before transport.
    pub(in super::super) returned: Vec<super::super::accounting::ReturnedStorage>,
    /// Source exits retained their own result origins and charges before the
    /// structural transfer template joined their returned forests.
    pub(in super::super) packed_returns: bool,
    /// Incoming guard and mutex binders come from executable formal parameters.
    pub(in super::super) synchronization_inputs: super::super::synchronization::parameters::Inputs,
    /// Owned protocol witnesses, their source bindings, and population proof dependencies.
    pub(in super::super) holders: super::super::synchronization::holders::Bindings,
    /// Pairs of formal mutex instances whose ownership updates require separate trees.
    pub(in super::super) distinct_payload_inputs: std::collections::BTreeSet<(usize, usize)>,
    /// Incoming regions moved into a private carried allocation. The closed
    /// consumer keeps the caller's full input charged through its return.
    pub(in super::super) carried_inputs: HashSet<usize>,
    /// This fixed collector owns the reservations carried by its captured handle slots.
    pub(in super::super) collection_claims:
        std::collections::BTreeMap<super::super::shared::RootId, Expr>,
    /// Worker checkpoints whose incoming shared backing belongs to an enclosing actor.
    pub(in super::super) shared_checkpoints: Vec<super::super::shared::phases::Checkpoint>,
    /// Retained workers require a complete occurrence transformation even when
    /// the enclosing function returns no owned value.
    pub(in super::super) retained_workers: bool,
    /// The owned vector passed through this helper and its original backing state.
    /// Each checked extraction splits the caller's input lifetimes.
    pub(in super::super) worker_parameter: Option<(usize, usize)>,
    /// Exit destinations accepted by lexical lifetime accounting.
    pub(in super::super) exits: HashMap<u64, crate::resource::memory::control::Target>,
    /// Shared loop structure and boundaries, published after body accounting.
    pub(in super::super) loops: HashMap<u64, crate::resource::memory::loops::Loop>,
    /// Conditional lifetime joins accepted by branch accounting.
    pub(in super::super) branches: HashMap<u64, Vec<InputChoice>>,
    /// Immutable worker-entry observations for captured populations. Body
    /// proofs use these snapshots; exported templates still bind caller inputs.
    pub(in super::super) captured_populations: HashMap<usize, Expr>,
    /// Original owned parameter nodes, before any runtime partitioning.
    pub(super) inputs: Vec<crate::resource::memory::paths::InputPath>,
    /// Borrowed originals have identities but remain charged outside this frame.
    pub(super) borrowed_inputs:
        std::collections::BTreeMap<usize, crate::resource::memory::paths::InputPath>,
    /// Final disjoint regions attached to the result and borrowed parameters.
    pub(super) outputs: super::Origins<usize>,
    /// Caller-side lifetime mappings published after a template is committed.
    pub(in super::super) call_origins: HashMap<u64, CallOrigins>,
    /// Constructor visits for fixed heap objects and logical vector backings.
    pub(in super::super) allocation_visits: HashMap<u64, super::super::workers::SourceVisit<AstId>>,
    /// Additional borrowed-input and operation-derived lifetime identities.
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
    pub(in super::super) fn publishes_at(
        &self,
        site: AstId,
        parameter: usize,
        interval: super::super::synchronization::local::Interval,
    ) -> bool {
        matches!(self.operations.get(&site), Some(Operation::Call { synchronization: Some(call), modified, .. })
            if modified.contains(&parameter) && call.published_section() == Some((parameter, interval)))
    }

    /// The caller frames the incoming allocations at the mutex. If a helper
    /// removes an original allocation and keeps it across unlock, the published
    /// mutex contents alone cannot describe its lifetime.
    pub(in super::super) fn release_retains_inputs(
        &self,
        parameter: usize,
        interval: super::super::synchronization::local::Interval,
        points: &[super::super::accounting::Point],
    ) -> bool {
        use super::super::synchronization::local::Boundary;
        let Some(output) = self.outputs.get(&Some(parameter)) else { return false };
        let mut found = false;
        for point in points
            .iter()
            .filter(|p| matches!(p.condition.boundary, Boundary::Release(id) if id == interval))
        {
            found = true;
            if point.call_point.is_some() {
                // A forwarding call can reuse the callee's checked release.
                // Its caller-side region identities are fresh at the return.
                if !matches!(self.operations.get(&point.span.id),
                    Some(Operation::Call { synchronization: Some(call), .. })
                        if call.single_release() == Some(interval))
                {
                    return false;
                }
            } else if !point.inputs.iter().all(|id| output.values().any(|out| out == id)) {
                return false;
            }
        }
        found
    }

    /// A single non-repeating acquisition can export its updated borrowed
    /// parameter on normal exit. A second acquisition could observe a peer's
    /// intervention before that exit, even when it locks the same mutex.
    pub(in super::super) fn closed_mutex_section(
        &self,
    ) -> Option<(usize, super::super::synchronization::local::Interval)> {
        use super::super::synchronization::{Instance, local::View};
        if self.retained_workers {
            return None;
        }
        let mut section = None;
        for op in self.operations.values() {
            let id = match op {
                Operation::MutexLock { interval, occurrence, .. } if occurrence.single_visit() => {
                    *interval
                }
                Operation::Call { synchronization: Some(call), .. }
                    if call.has_fresh_acquisitions() =>
                {
                    call.single_release()?
                }
                Operation::MutexLock { .. }
                | Operation::WorkerPublish(_)
                | Operation::WorkerJoin { .. }
                | Operation::ParameterJoin { .. } => return None,
                _ => continue,
            };
            if section.replace(id).is_some() {
                return None;
            }
        }
        let interval = section?;
        let Instance::Input(index) = interval.instance else { return None };
        if self.synchronization_inputs.input_view(index) != Some(View::Mutex(interval.instance))
            || self.payload_borrows() != [interval].into()
        {
            return None;
        }
        Some((index, interval))
    }

    pub(in super::super) fn acquires_at_visit(
        &self,
        id: super::super::synchronization::local::Interval,
        visit: &super::super::workers::SourceVisit<AstId>,
    ) -> bool {
        self.operations.values().any(|op| match op {
            Operation::RwWrite { acquired: Some((interval, occurrence)), .. } => {
                *interval == id && occurrence.same_visit_scope(visit)
            }
            Operation::MutexLock { interval, occurrence, .. } => {
                *interval == id && occurrence.same_visit_scope(visit)
            }
            Operation::Call { synchronization: Some(call), .. } => {
                call.acquires_at_visit(id, visit)
            }
            _ => false,
        })
    }

    /// Only a checked native acquisition of one concrete mutex can exclude
    /// another fixed worker phase on that mutex.
    pub(in super::super) fn mutex_intervals(
        &self,
        caller: &Self,
    ) -> impl Iterator<Item = super::super::synchronization::local::Interval> + '_ {
        // A constructor in the caller outside repeated visits names a single
        // runtime object across the entire worker population. A repeated
        // constructor or a lock private to each child gives no such exclusion.
        let shared: std::collections::BTreeSet<_> = caller
            .operations
            .values()
            .filter_map(|op| match op {
                Operation::MutexNew { instance, occurrence, .. } if occurrence.single_visit() => {
                    Some(*instance)
                }
                _ => None,
            })
            .collect();
        self.operations.values().filter_map(move |operation| match operation {
            Operation::MutexLock { interval, occurrence, .. }
                if (occurrence.single_visit() || shared.contains(&interval.instance))
                    && matches!(
                        interval.instance,
                        super::super::synchronization::Instance::Fresh(_)
                    ) =>
            {
                Some(*interval)
            }
            _ => None,
        })
    }

    pub(in super::super) fn locks_mutex(&self) -> bool {
        self.synchronization_inputs.has_guards()
            || self.operations.values().any(|op| match op {
                Operation::MutexLock { .. } => true,
                Operation::Call { synchronization: Some(call), .. } => call.has_intervals(),
                _ => false,
            })
    }

    /// A guard-consuming helper may publish its caller's unchanged contents
    /// only when neither it nor a nested helper accessed that acquisition.
    pub(in super::super) fn payload_borrows(
        &self,
    ) -> std::collections::BTreeSet<super::super::synchronization::local::Interval> {
        let mut borrows = std::collections::BTreeSet::new();
        for op in self.operations.values() {
            match op {
                Operation::GuardBorrow { interval, .. } => {
                    borrows.insert(*interval);
                }
                Operation::Call { synchronization: Some(call), .. } => {
                    borrows.extend(&call.payload_borrows);
                }
                _ => {}
            }
        }
        borrows
    }

    /// Validate native construction and acquisition binders once per body.
    pub(in super::super) fn interval_binders(
        &self,
        span: &crate::messages::Span,
        actor: Option<super::super::workers::WorkerId>,
    ) -> Result<std::collections::BTreeSet<super::super::synchronization::local::Interval>, VirErr>
    {
        let mut instances = std::collections::BTreeSet::new();
        let mut intervals = self.synchronization_inputs.intervals();
        let mut attempts = std::collections::BTreeSet::new();
        for (site, operation) in &self.operations {
            let (occurrence, fresh) = match operation {
                Operation::WorkerJoin { mutex_receipt: Some(receipt), .. } => {
                    if !receipt.valid_for(*site, actor) {
                        return Err(super::super::model::unsupported(
                            span,
                            "a mutex receipt outside its selected join",
                        ));
                    }
                    continue;
                }
                Operation::Call { synchronization: Some(call), .. } => {
                    call.validate(*site, actor, &mut intervals, &mut attempts, span)?;
                    continue;
                }
                Operation::RwWrite {
                    acquired: Some((interval, visit)), replacement: None, ..
                } => {
                    if *site != visit.site
                        || !visit.valid_for(actor)
                        || !intervals.insert(*interval)
                    {
                        return Err(super::super::model::unsupported(
                            span,
                            "an invalid verified writer acquisition",
                        ));
                    }
                    continue;
                }
                Operation::MutexNew { instance, occurrence, .. } => {
                    (occurrence, instances.insert(*instance))
                }
                Operation::MutexLock { interval, occurrence, .. } => {
                    if occurrence.site.operation
                        == super::super::synchronization::Operation::MutexTryLock
                    {
                        attempts.insert(*interval);
                    }
                    (occurrence, intervals.insert(*interval))
                }
                _ => continue,
            };
            if !fresh || occurrence.site.anchor != *site || !occurrence.valid_for(actor) {
                return Err(super::super::model::unsupported(
                    span,
                    "an invalid synchronization occurrence binder",
                ));
            }
        }
        for operation in self.operations.values() {
            if let Operation::GuardBorrow { interval, .. } = operation
                && !intervals.contains(interval)
            {
                return Err(super::super::model::unsupported(
                    span,
                    "a protected borrow without its acquisition occurrence",
                ));
            }
        }
        for pattern in self.patterns.values() {
            if let Pattern::LockOutcome { interval, acquired } = pattern
                && (!intervals.contains(interval)
                    || *acquired != Some(true) && !attempts.contains(interval))
            {
                return Err(super::super::model::unsupported(
                    span,
                    "a lock pattern incompatible with its native acquisition",
                ));
            }
        }
        Ok(intervals)
    }

    /// Local construction outside the actor's repeatable loops.
    pub(in super::super) fn owns_fixed_root(&self, root: super::super::shared::RootId) -> bool {
        self.fixed_shared_payload(root).is_some()
    }

    /// Constructor operand of a single coordinator-owned Arc allocation.
    pub(in super::super) fn fixed_shared_payload(
        &self,
        id: super::super::shared::RootId,
    ) -> Option<&Expr> {
        self.operations.values().find_map(|op| match op {
            Operation::StrongNew { root, payload, coordinates }
                if *root == id && coordinates.is_empty() =>
            {
                Some(payload)
            }
            _ => None,
        })
    }

    /// This join recovered the payload of a uniquely transported Arc.
    pub(in super::super) fn recovered_payload(&self, root: super::super::shared::RootId) -> bool {
        self.operations.values().any(
            |op| matches!(op, Operation::WorkerJoin { payload_handle: Some(id), .. } if *id == root),
        )
    }

    /// Executable constructor at which the per-visit publication count resets.
    pub(in super::super) fn shared_constructor(
        &self,
        root: super::super::shared::RootId,
    ) -> Option<(u64, &[(u64, Expr)])> {
        self.operations.iter().find_map(|(site, op)| match op {
            Operation::StrongNew { root: owned, coordinates, .. } if *owned == root => {
                Some((*site, coordinates.as_slice()))
            }
            _ => None,
        })
    }

    /// The input backing can be reused only while all changes to its indexed
    /// contents are checked removals. Local moves preserve the storage identity.
    pub(in super::super) fn forwards_worker_vector(&self, helper: impl Fn(&Fun) -> bool) -> bool {
        self.assignments.values().all(|assignment| assignment.destination.location.1.is_empty())
            && self.operations.values().all(|op| {
                matches!(
                    op,
                    Operation::Length { .. }
                        | Operation::Remove { input: Some(_), .. }
                        | Operation::Unwrap { .. }
                        | Operation::Drop { .. }
                        | Operation::ParameterJoin { .. }
                        | Operation::Evaluate { .. }
                ) || matches!(op, Operation::Call { target, .. } if helper(target))
            })
    }

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

    /// Derived lifetimes require a template even behind a fixed or unit result.
    pub(super) fn has_regions(&self) -> bool {
        self.regions != 0
    }

    pub(in super::super) fn operation(&mut self, span: &Span, operation: Operation) {
        match &operation {
            Operation::Closure { captures } => {
                for (mode, capture) in captures {
                    if *mode == super::super::concurrency::CaptureMode::Move {
                        self.mutations.push(capture.location.clone());
                    }
                }
            }
            Operation::RwWrite { slot, .. } => self.mutations.push(slot.location.clone()),
            Operation::Push { receiver, .. } | Operation::Remove { receiver, .. } => {
                self.mutations.push(receiver.location.clone());
            }
            Operation::Call { borrowed, modified, synchronization, .. } => {
                if let Some(call) = synchronization {
                    self.distinct_payload_inputs.extend(&call.distinct_inputs);
                }
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

    /// Logical owner changes matter even when they allocate no new bytes.
    pub(super) fn mutates(&self, name: &VarIdent) -> bool {
        self.mutations.iter().any(|(root, _)| root == name)
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

    pub(in super::super) fn covered(&self, used: &HashSet<(Kind, u64)>) -> bool {
        self.branches.keys().all(|id| used.contains(&(Kind::Branch, *id)))
            && self.operations.keys().all(|id| used.contains(&(Kind::Operation, *id)))
            && self.moves.keys().all(|id| used.contains(&(Kind::Move, *id)))
            && self.assignments.keys().all(|id| used.contains(&(Kind::Assign, *id)))
            && self.patterns.keys().all(|id| used.contains(&(Kind::Pattern, *id)))
            && self.scopes.keys().all(|id| used.contains(&(Kind::Scope, *id)))
            && self.loops.keys().all(|id| used.contains(&(Kind::Loop, *id)))
            && self.exits.keys().all(|id| used.contains(&(Kind::Exit, *id)))
    }
}
