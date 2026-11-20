//! Synchronization contracts and acquisition identities for memory effects.
//!
//! Exclusion is supplied by a reviewed primitive contract or (eventually) a
//! checked protocol certificate. It never releases allocation charges. This
//! module deliberately has no operation that changes allocation accounting.
//! The standard contract targets the pinned Rust 1.99.1 library and assumes its
//! mutex/guard semantics and Rust ownership/Send checks. Acquire may block and
//! poison outcomes retain guards; neither success nor a user invariant is assumed.

use crate::ast::{Dt, VarIdent};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use vir_macros::ToDebugSNode;

pub mod flow;

/// Compiler-identified synchronization operations, independent of source names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, ToDebugSNode)]
pub enum Operation {
    /// Construct a fresh, initially unpoisoned mutex instance.
    MutexNew,
    /// Acquire, possibly blocking; reentrant blocking lock is unsupported.
    MutexLock,
    /// Attempt acquisition; WouldBlock produces no acquisition.
    MutexTryLock,
    /// Borrow the payload through an existing guard, without another acquisition.
    GuardBorrow,
    /// Mutably borrow the payload through an existing guard.
    GuardBorrowMut,
    /// Release at actual destructor execution, not at last use.
    GuardDrop,
}

/// Opaque library layouts recognized by resolved datatype identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LibraryType {
    /// `Mutex<T>`, with state, poison flag and inline T.
    Mutex,
    /// `MutexGuard<T>`, an inline reference with a release effect.
    MutexGuard,
    /// `PoisonError<T>`, whose active payload can itself be a guard.
    PoisonError,
    /// `TryLockError<T>`, with Poisoned(T) or WouldBlock.
    TryLockError,
    /// Standard `Result<T, E>`; sizing alone gives no ownership interface.
    Result,
    /// Native Rust join handle; its completion record is separate storage.
    StdJoinHandle,
    /// Reviewed vstd join wrapper, with the same source handle size.
    VstdJoinHandle,
}

/// Resolved library identities; unrelated types cannot receive opaque layouts.
pub type LibraryTypes = HashMap<Dt, LibraryType>;

/// Frontend evidence, kept separate from user specifications and checked memory
/// summaries. A cleanup graph alone never establishes an allocation lifetime or
/// a concurrent byte bound.
#[derive(Default)]
pub struct CompilerEvidence {
    /// Worker captures and executable operations hidden by logical identity erasure.
    pub concurrency: super::concurrency::Evidence,
    /// Resolved native types used for source layouts and primitive contracts.
    pub types: LibraryTypes,
    /// Drop-elaborated transport for local resource-contracted functions.
    pub cleanup: HashMap<crate::ast::Fun, flow::Graph>,
}

impl CompilerEvidence {
    /// Resolve a compiler graph in its original function-local namespace.
    /// A closure and its enclosing function have separate graphs; no missing
    /// graph or reused local index can establish executable effects.
    pub fn graph(&self, function: &crate::ast::Fun) -> Option<&flow::Graph> {
        self.cleanup.get(function).or_else(|| {
            self.concurrency
                .closures
                .values()
                .find(|closure| closure.function == *function)
                .map(|closure| &closure.body)
        })
    }
}

/// Possible outcomes of an acquire operation. Poisoned still owns the lock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// A successful acquisition.
    Acquired,
    /// An acquisition carrying a poison error; not proof of a user invariant.
    Poisoned,
    /// A non-acquiring try-lock failure.
    WouldBlock,
}

/// Immutable capacity substituted when a protocol summary is instantiated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Capacity {
    /// A fixed protocol capacity.
    Constant(u64),
    /// A constructor/summary scalar input, requiring the usual range proof.
    Input(usize),
    /// Immutable capacity metadata of the projected protocol instance, supplied
    /// by its checked constructor/summary rather than a caller-written counter.
    Instance,
}

/// A contract's bound on simultaneously outstanding acquisitions of one instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Holders {
    /// At most one independent acquisition is outstanding.
    Exclusive,
    /// An immutable permit capacity, possibly symbolic. This is not a byte budget.
    Bounded(Capacity),
}

/// Reviewed primitive guarantees. Construction is private to the trusted registry.
#[derive(Clone, Copy, Debug)]
pub struct Contract {
    holders: Holders,
    may_block: bool,
    may_poison: bool,
}

impl Operation {
    /// Obtain the registry contract only for an acquisition operation.
    pub fn acquisition_contract(self) -> Option<Contract> {
        match self {
            Self::MutexLock | Self::MutexTryLock => Some(Contract {
                holders: Holders::Exclusive,
                may_block: self == Self::MutexLock,
                may_poison: true,
            }),
            _ => None,
        }
    }
}

impl Contract {
    /// The simultaneous-holder guarantee, independent of allocation size.
    pub fn holders(self) -> Holders {
        self.holders
    }

    /// Whether the operation may wait with all its caller storage still live.
    pub fn may_block(self) -> bool {
        self.may_block
    }

    /// Whether an acquiring poison outcome must be represented or excluded by proof.
    pub fn may_poison(self) -> bool {
        self.may_poison
    }
}

/// Instance identity within one summary. Input identities are binders: different
/// input indices do not prove that actual instances are distinct.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Instance {
    /// An instance supplied by a caller, substituted with its actual identity.
    Input(usize),
    /// A construction site, freshened on summary instantiation and loop visits.
    Fresh(u64),
}

/// One acquired interval. A fresh interval is required after every release.
/// Summary instantiation must freshen these identities along with instance sites.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Acquisition(u64);

/// Acquisition lifecycle events, which never imply deallocation of a buffer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Event {
    /// An acquiring result, including the poison case, begins an interval.
    Acquire {
        /// Stable lock/protocol instance.
        instance: Instance,
        /// The individual interval created by this outcome.
        acquisition: Acquisition,
        /// Acquired or Poisoned; WouldBlock has no such event.
        outcome: Outcome,
    },
    /// A consumed guard ends its acquired interval.
    Release {
        /// Stable lock/protocol instance.
        instance: Instance,
        /// The exact interval ended by actual release.
        acquisition: Acquisition,
    },
}

#[derive(Clone, Copy, Debug)]
enum Binding {
    Instance(Instance),
    Guard(Instance, Acquisition),
    View(Instance, Acquisition),
}

/// Structural effect errors. None can be repaired by increasing a byte allowance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EffectError {
    /// No instance or live guard is known at this place.
    UnknownBinding,
    /// A destination still holds an identity whose cleanup has not been recorded.
    OccupiedBinding,
    /// A borrowed guard view cannot release the owned acquisition.
    BorrowedRelease,
    /// A blocking acquire would reenter an instance with a known live guard.
    ReentrantAcquire,
    /// The outcome contradicts the operation or a known outstanding acquisition.
    InvalidOutcome,
    /// Compiler site IDs exceeded their representable range.
    IdentityOverflow,
}

/// Local identity transport and acquired-interval effects. This is not a global
/// holder-count proof: input alias constraints and interference belong to the
/// checked summary and protocol proof, not assumptions made by this state.
#[derive(Debug, Default)]
pub struct Effects {
    next: u64,
    bindings: HashMap<VarIdent, Binding>,
    events: Vec<Event>,
}

impl Effects {
    fn fresh(&mut self) -> Result<u64, EffectError> {
        let id = self.next;
        self.next = id.checked_add(1).ok_or(EffectError::IdentityOverflow)?;
        Ok(id)
    }

    fn vacant(&self, name: &VarIdent) -> Result<(), EffectError> {
        if self.bindings.contains_key(name) { Err(EffectError::OccupiedBinding) } else { Ok(()) }
    }

    /// Bind a caller's symbolic instance. Equal actual arguments must be unified
    /// during instantiation; distinct binders alone supply no disequality proof.
    pub fn input(&mut self, name: VarIdent, index: usize) -> Result<(), EffectError> {
        self.vacant(&name)?;
        self.bindings.insert(name, Binding::Instance(Instance::Input(index)));
        Ok(())
    }

    /// Bind a newly constructed instance site.
    pub fn construct(&mut self, name: VarIdent) -> Result<Instance, EffectError> {
        self.vacant(&name)?;
        let instance = Instance::Fresh(self.fresh()?);
        self.bindings.insert(name, Binding::Instance(instance));
        Ok(instance)
    }

    /// Preserve identity through an alias or a borrowed guard view.
    pub fn borrow(&mut self, source: &VarIdent, destination: VarIdent) -> Result<(), EffectError> {
        self.vacant(&destination)?;
        let binding = match self.bindings.get(source).ok_or(EffectError::UnknownBinding)? {
            Binding::Instance(instance) => Binding::Instance(*instance),
            Binding::Guard(instance, acquisition) | Binding::View(instance, acquisition) => {
                Binding::View(*instance, *acquisition)
            }
        };
        self.bindings.insert(destination, binding);
        Ok(())
    }

    /// Transfer an owned binding without creating a new instance/acquisition.
    pub fn move_to(&mut self, source: &VarIdent, destination: VarIdent) -> Result<(), EffectError> {
        self.vacant(&destination)?;
        let binding = self.bindings.remove(source).ok_or(EffectError::UnknownBinding)?;
        self.bindings.insert(destination, binding);
        Ok(())
    }

    /// Resolve a lock alias. An unresolved relation must remain unresolved.
    pub fn instance(&self, name: &VarIdent) -> Option<Instance> {
        match self.bindings.get(name)? {
            Binding::Instance(instance)
            | Binding::Guard(instance, _)
            | Binding::View(instance, _) => Some(*instance),
        }
    }

    /// Record an outcome only on the corresponding control-flow edge. Callers
    /// must never select Acquired merely because the operation was named lock.
    pub fn acquire(
        &mut self,
        source: &VarIdent,
        destination: VarIdent,
        operation: Operation,
        outcome: Outcome,
    ) -> Result<Option<Acquisition>, EffectError> {
        self.vacant(&destination)?;
        let contract = operation.acquisition_contract().ok_or(EffectError::InvalidOutcome)?;
        let Some(Binding::Instance(instance)) = self.bindings.get(source).copied() else {
            return Err(EffectError::UnknownBinding);
        };
        let held = self
            .bindings
            .values()
            .any(|binding| matches!(binding, Binding::Guard(other, _) if *other == instance));
        if contract.may_block && held {
            return Err(EffectError::ReentrantAcquire);
        }
        if outcome == Outcome::WouldBlock {
            return if contract.may_block { Err(EffectError::InvalidOutcome) } else { Ok(None) };
        }
        // A known held lock cannot be acquired again by try_lock either.
        if held {
            return Err(EffectError::InvalidOutcome);
        }
        let acquisition = Acquisition(self.fresh()?);
        self.bindings.insert(destination, Binding::Guard(instance, acquisition));
        self.events.push(Event::Acquire { instance, acquisition, outcome });
        Ok(Some(acquisition))
    }

    /// Release at an actual destructor/release event. A borrowed view cannot
    /// release an acquisition. Outstanding allocations are deliberately untouched.
    pub fn release(&mut self, name: &VarIdent) -> Result<(), EffectError> {
        let binding = *self.bindings.get(name).ok_or(EffectError::UnknownBinding)?;
        let Binding::Guard(instance, acquisition) = binding else {
            return Err(EffectError::BorrowedRelease);
        };
        self.bindings.remove(name);
        self.bindings
            .retain(|_, binding| !matches!(binding, Binding::View(_, id) if *id == acquisition));
        self.events.push(Event::Release { instance, acquisition });
        Ok(())
    }

    /// Ordered lifecycle evidence, for the graph builder rather than a byte counter.
    pub fn events(&self) -> &[Event] {
        &self.events
    }
}

/// A projection into an input or output ownership tree of a protocol operation.
#[derive(Clone, Debug)]
pub struct Projection {
    /// Parameter index; None denotes the returned value.
    pub parameter: Option<usize>,
    /// Fixed field path to the instance or tracked witness.
    pub fields: Vec<crate::ast::Ident>,
}

/// One result edge of a declared protocol transition. Its condition must be
/// related to the executable result by verification, not assumed by the caller.
#[derive(Clone, Debug)]
pub struct ProtocolOutcome {
    /// Executable result predicate selecting this edge.
    pub condition: crate::ast::Expr,
    /// Tracked witnesses consumed on this edge.
    pub consumes: Vec<Projection>,
    /// Tracked witnesses produced on this edge.
    pub produces: Vec<Projection>,
}

/// Unchecked declaration schema. It conveys no guarantees until a later protocol
/// checker proves initialization, transition refinement, witness conservation,
/// encapsulation and interference stability. There is intentionally no conversion
/// from this public declaration into the private trusted Contract representation.
#[derive(Clone, Debug)]
pub struct ProtocolDeclaration {
    /// Executable function whose synchronization effects are described.
    pub operation: crate::ast::Fun,
    /// Executable instance whose synchronization effects are described.
    pub instance: Projection,
    /// User invariant that the protocol's initialization/transitions must prove.
    pub invariant: crate::ast::Fun,
    /// Result-dependent transitions, including non-acquiring failure outcomes.
    pub outcomes: Vec<ProtocolOutcome>,
    /// Claimed holder property, requiring protocol proof rather than trust.
    pub holders: Holders,
}

#[cfg(test)]
mod tests;

/// Whether a function needs executable synchronization cleanup evidence.
/// Proof-only values and type-only size queries do not require a compiler body.
pub fn needs_cleanup(
    function: &crate::ast::Function,
    modes: Option<&crate::resolution_inference::ResolutionInfo>,
    types: &LibraryTypes,
    datatypes: &[crate::ast::Datatype],
) -> bool {
    let empty = HashMap::new();
    let modes = modes.map(|m| &m.var_modes).unwrap_or(&empty);
    super::closures::needs_evidence(function, modes)
        || reject_unaccounted_inner(function, modes, types, datatypes, false, false).is_err()
}

/// Distinguish executable roots from tracked protocol witnesses and specification
/// bindings. Lifetime-check MIR preserves proof code: its presence must never
/// confer a runtime guard, byte charge or native exclusion guarantee.
pub fn attach_binding_modes(
    graph: &mut flow::Graph,
    function: &crate::ast::Function,
    modes: Option<&crate::resolution_inference::ResolutionInfo>,
) {
    for (name, binding) in &mut graph.bindings {
        binding.mode = modes
            .and_then(|m| m.var_modes.get(name))
            .copied()
            .or_else(|| function.x.params.iter().find(|p| p.x.name == *name).map(|p| p.x.mode));
    }
}

/// Recognizing primitive layouts, exclusion and cleanup does not establish
/// allocation coverage or asynchronous storage. Reject runtime use until those passes
/// are connected. Type-only size queries remain available without such a proof.
pub(super) fn reject_unaccounted(
    function: &crate::ast::Function,
    modes: &HashMap<VarIdent, crate::ast::Mode>,
    types: &LibraryTypes,
    datatypes: &[crate::ast::Datatype],
    worker_parameter: bool,
) -> Result<(), crate::ast::VirErr> {
    reject_unaccounted_inner(function, modes, types, datatypes, true, worker_parameter)
}

/// Evidence collection still observes supported shared operations. Their logical
/// erasure and runtime cleanup must be recovered even after their storage paths
/// are accounted, independently of the remaining synchronization/worker gate.
fn reject_unaccounted_inner(
    function: &crate::ast::Function,
    modes: &HashMap<VarIdent, crate::ast::Mode>,
    types: &LibraryTypes,
    datatypes: &[crate::ast::Datatype],
    shared_accounted: bool,
    worker_parameter: bool,
) -> Result<(), crate::ast::VirErr> {
    use crate::ast::*;
    use crate::ast_visitor::{AstVisitor, NoScoper, Walk};
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum SharedCheck {
        Evidence,
        Local,
        Input,
        Output,
    }
    struct Check<'a> {
        modes: &'a HashMap<VarIdent, Mode>,
        types: &'a LibraryTypes,
        datatypes: HashMap<crate::ast::Dt, &'a crate::ast::Datatype>,
        shared: SharedCheck,
        worker_parameter: bool,
    }
    impl Check<'_> {
        fn runtime_type(&self, typ: &Typ, span: &crate::messages::Span) -> Result<(), VirErr> {
            self.runtime_type_inner(typ, span, &mut std::collections::HashSet::new())
        }
        fn runtime_type_inner(
            &self,
            typ: &Typ,
            span: &crate::messages::Span,
            visiting: &mut std::collections::HashSet<Dt>,
        ) -> Result<(), VirErr> {
            match &**typ {
                TypX::Decorate(TypDecoration::Ghost | TypDecoration::Tracked, _, _) => {
                    return Ok(());
                }
                TypX::Decorate(TypDecoration::Arc, _, inner) => {
                    if self.shared != SharedCheck::Local {
                        return Err(super::model::unsupported(
                            span,
                            match self.shared {
                                SharedCheck::Input => {
                                    "shared input roots without a checked alias descriptor"
                                }
                                SharedCheck::Output => {
                                    "shared results without a checked outgoing alias descriptor"
                                }
                                _ => {
                                    "runtime shared ownership requires executable lifetime evidence"
                                }
                            },
                        ));
                    }
                    self.runtime_type_inner(inner, span, visiting)?;
                }
                TypX::Datatype(name, args, _) => {
                    // A forwarding helper owns the handle, not its future
                    // payload. Opening a handle still needs a checked join.
                    if self.worker_parameter
                        && self.types.get(name).is_some_and(|kind| {
                            matches!(kind, LibraryType::StdJoinHandle | LibraryType::VstdJoinHandle)
                        })
                    {
                        return Ok(());
                    }
                    if self.types.get(name).is_some_and(|kind| {
                        *kind != LibraryType::Result
                            && !(self.shared == SharedCheck::Local && *kind == LibraryType::Mutex)
                    }) {
                        return Err(super::model::unsupported(
                            span,
                            "runtime synchronization values before concurrent lifetime accounting is available",
                        ));
                    }
                    for arg in args.iter() {
                        self.runtime_type_inner(arg, span, visiting)?;
                    }
                    if visiting.insert(name.clone()) {
                        if let Some(datatype) = self.datatypes.get(name) {
                            for variant in datatype.x.variants.iter() {
                                for field in variant.fields.iter().filter(|f| f.a.1 == Mode::Exec) {
                                    self.runtime_type_inner(&field.a.0, span, visiting)?;
                                }
                            }
                        }
                        visiting.remove(name);
                    }
                }
                TypX::Decorate(_, _, inner) | TypX::MutRef(inner) => {
                    self.runtime_type_inner(inner, span, visiting)?
                }
                TypX::Primitive(_, args) => {
                    for arg in args.iter() {
                        self.runtime_type_inner(arg, span, visiting)?;
                    }
                }
                _ => {}
            }
            Ok(())
        }
    }
    impl AstVisitor<Walk, VirErr, NoScoper> for Check<'_> {
        fn visit_typ(&mut self, _: &Typ) -> Result<(), VirErr> {
            // Generic arguments of type-only size queries are not runtime values.
            Ok(())
        }
        fn visit_expr(&mut self, expr: &Expr) -> Result<(), VirErr> {
            if super::execution::ignored_expression(expr) {
                return Ok(());
            }
            if matches!(expr.x, ExprX::NonSpecClosure { .. }) {
                // Creation transfers its executable captures. The body runs
                // only through an accounted invocation/publication boundary.
                return Ok(());
            }
            if let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), .. } = &expr.x
                && let Some(ResourceIntrinsic::Synchronization(operation)) =
                    attrs.resource_intrinsic
                && !(self.shared == SharedCheck::Local && operation == Operation::MutexNew)
            {
                return Err(super::model::unsupported(
                    &expr.span,
                    &format!(
                        "synchronization operation {operation:?} before concurrent lifetime accounting is available"
                    ),
                ));
            }
            if let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), .. } = &expr.x
                && let Some(ResourceIntrinsic::Concurrency(operation)) = attrs.resource_intrinsic
            {
                if self.shared != SharedCheck::Local
                    || !(self.worker_parameter && operation.joins())
                        && !matches!(
                            operation,
                            super::concurrency::Operation::ArcNew
                                | super::concurrency::Operation::ArcClone
                                | super::concurrency::Operation::ArcIntoInner
                                | super::concurrency::Operation::ArcBorrow
                        )
                {
                    return Err(super::model::unsupported(
                        &expr.span,
                        &format!(
                            "concurrent operation {operation:?} before concurrent lifetime accounting is available"
                        ),
                    ));
                }
            }
            self.runtime_type(&expr.typ, &expr.span)?;
            self.visit_expr_rec(expr)
        }
        fn visit_stmt(&mut self, statement: &Stmt) -> Result<(), VirErr> {
            if super::execution::ignored_statement(statement, self.modes) {
                return Ok(());
            }
            self.visit_stmt_rec(statement)
        }
        fn visit_place(&mut self, place: &Place) -> Result<(), VirErr> {
            self.visit_place_rec(place)
        }
        fn visit_pattern(&mut self, _: &Pattern) -> Result<(), VirErr> {
            Ok(())
        }
    }
    let mut check = Check {
        modes,
        types,
        datatypes: datatypes.iter().map(|d| (d.x.name.clone(), d)).collect(),
        worker_parameter,
        shared: if shared_accounted { SharedCheck::Input } else { SharedCheck::Evidence },
    };
    for parameter in function.x.params.iter().filter(|p| p.x.mode == Mode::Exec) {
        check.runtime_type(&parameter.x.typ, &parameter.span)?;
    }
    if shared_accounted {
        check.shared = SharedCheck::Output;
    }
    check.runtime_type(&function.x.outer_ret.x.typ, &function.span)?;
    if shared_accounted {
        check.shared = SharedCheck::Local;
    }
    if let Some(body) = &function.x.body {
        check.visit_expr(body)?;
    }
    Ok(())
}
