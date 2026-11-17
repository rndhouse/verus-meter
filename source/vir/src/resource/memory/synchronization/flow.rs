//! Compiler-derived transport and cleanup, before any footprint attribution.
//!
//! Places are function-local binders, not addresses. Assignments are identity
//! equations on the corresponding control-flow edge: moving a guard transfers its
//! acquisition, borrowing it creates a view, and a drop consumes only the owned
//! acquisition at that place. Neither StorageDead nor last use is a release.
//! Consumers must preserve branches and loops and freshen construction/acquisition
//! sites on dynamic visits. This graph supplies no byte-accounting exemption.

use super::{Operation, Outcome};
use crate::ast::{Fun, Mode, VarIdent};
use crate::messages::Span;
use std::collections::HashMap;

/// One compiler place, including temporaries and the return slot (local zero).
/// Different places can refer to the same instance: input/borrow aliasing must
/// be resolved before using exclusion, never inferred from binder inequality.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place {
    /// Local binder within this function, freshened at summary instantiation.
    pub local: usize,
    /// Ordered projections, preserving variant and field identity.
    pub projection: Vec<Projection>,
}

/// Structural projections admitted by synchronization identity transport.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Projection {
    /// Follow a reference; this does not create an owned guard.
    Deref,
    /// Select a fixed field of the current aggregate or variant.
    Field(usize),
    /// Restrict to a particular active enum variant on a checked control edge.
    Variant(usize),
}

/// An operand retains Rust's distinction between ownership transfer and copying.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    /// Consumes the source place on this edge.
    Move(Place),
    /// Copies a reference/scalar; this cannot duplicate an owned acquisition.
    Copy(Place),
    /// Scalar value, including compiler-generated drop flags.
    Scalar(u128),
    /// Other constant; it cannot manufacture a synchronization identity.
    Constant,
    /// An unsupported projected operand; it cannot be treated as a constant.
    Unsupported,
}

/// Identity transport at an assignment. Unsupported transport is explicit and
/// must be discharged or rejected before a graph supplies exclusion facts.
#[derive(Clone, Debug)]
pub enum Value {
    /// Move or copy, as selected by the operand.
    Use(Operand),
    /// A reference to an existing place; no capacity is acquired.
    Borrow(Place),
    /// Construct a fixed-field aggregate, retaining each operand's ownership.
    Aggregate {
        /// Active enum variant, if any.
        variant: Option<usize>,
        /// Operands in declaration order.
        fields: Vec<Operand>,
    },
    /// Read an enum tag. Branching on it preserves acquiring/failing outcomes.
    Discriminant(Place),
    /// Ordinary computation. It supplies no synchronization provenance.
    Other,
    /// Unsupported identity transport; never infer that its effects are empty.
    Unsupported,
}

/// Statements in executable order, retaining even storage endings that do not
/// execute destructors. Allocation accounting remains the memory pass's job.
#[derive(Clone, Debug)]
pub enum Statement {
    /// An assignment, including moves into temporaries and wrapper fields.
    Assign(Place, Value),
    /// A local becomes uninitialized. This is not an acquire or release.
    StorageLive(usize),
    /// A local's storage ends. A preceding actual drop supplies any release.
    StorageDead(usize),
    /// Set an enum tag during construction or compiler drop elaboration.
    SetDiscriminant(Place, usize),
    /// Compiler bookkeeping with no executable identity effect.
    Nop,
    /// An unmodeled executable operation, retained as a coverage obligation.
    Unsupported,
}

/// A location is also a static construction/acquisition site. It is not a
/// dynamic identity: loops, workers and calls must freshen each occurrence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Point {
    /// Compiler basic-block index.
    pub block: usize,
    /// Statement index, or the block's statement count for its terminator.
    pub statement: usize,
}

/// Keep unwind edges visible even though memory contracts require panic-free
/// user execution. A normal return never proves that the unwind edge is absent.
#[derive(Clone, Debug)]
pub enum Unwind {
    /// Execute the specified cleanup block.
    Cleanup(usize),
    /// No local cleanup (propagate, terminate, or compiler-proven unreachable).
    Exit,
}

/// Calls remain boundaries. Ordinary functional specifications cannot silently
/// confer primitive effects; helpers require checked summaries in the memory pass.
#[derive(Clone, Debug)]
pub enum Call {
    /// A resolved and reviewed synchronization primitive.
    Primitive(Operation),
    /// Worker/shared-owner operations; publication is not a completed helper call.
    Concurrent(super::super::concurrency::Operation),
    /// Statically identified closure invocation. The source call convention and
    /// a checked body summary must justify its ownership and cleanup effects.
    Closure(Fun),
    /// Actual `core::mem::drop`: consume the argument and execute its drop glue.
    Drop,
    /// A resolved helper or unsupported external function.
    Function(Fun),
    /// Indirect calls must be resolved or rejected before using this graph.
    Indirect,
}

/// An executable variant test selecting one primitive acquisition outcome.
#[derive(Clone, Debug)]
pub struct TagTest {
    /// Result or nested error enum whose tag is inspected.
    pub place: Place,
    /// Actual Rust discriminant value, not an assumed variant ordinal.
    pub discriminant: u128,
}

/// Conditional ownership produced by a native acquisition. The containing call
/// point supplies a fresh acquisition on each dynamic acquiring occurrence.
#[derive(Clone, Debug)]
pub struct AcquisitionOutcome {
    /// Success, acquiring poison, or non-acquiring WouldBlock.
    pub outcome: Outcome,
    /// Conjunction of compiler-derived enum tag tests selecting this outcome.
    pub conditions: Vec<TagTest>,
    /// Owned guard projection, absent only for non-acquiring failure. It remains
    /// owned by the result/error until an actual move or drop changes ownership.
    pub guard: Option<Place>,
}

/// Control flow is retained instead of flattening alternative outcomes into
/// simultaneous effects. In particular, WouldBlock never produces an acquisition.
#[derive(Clone, Debug)]
pub enum Terminator {
    /// Continue in another block.
    Goto(usize),
    /// Follow the matching scalar/tag edge, or otherwise.
    Switch {
        /// Operand being tested, potentially an acquisition result's tag.
        operand: Operand,
        /// Exact discriminant values and destinations from the compiler.
        targets: Vec<(u128, usize)>,
        /// Destination for all other values.
        otherwise: usize,
    },
    /// Execute a call; arguments move before callee execution, and the result is
    /// available only on the normal edge. Blocking retains all caller storage.
    Call {
        /// Resolved operation classification.
        call: Call,
        /// Arguments, preserving ownership and reference identities.
        arguments: Vec<Operand>,
        /// Destination of the normal result.
        destination: Place,
        /// Complete, mutually exclusive result alternatives for an acquisition;
        /// empty for other calls. No caller may arbitrarily select success.
        outcomes: Vec<AcquisitionOutcome>,
        /// Normal successor, absent for a diverging call.
        next: Option<usize>,
        /// Exceptional continuation; do not assume it is unreachable.
        unwind: Unwind,
    },
    /// Execute actual drop glue for this owned place. Dropping a reference does
    /// not release its pointee; dropping a wrapper follows its active ownership
    /// tree. Custom Drop bodies require their own checked effects.
    Drop {
        /// Place whose destructor runs, not its last-use site.
        place: Place,
        /// Normal continuation after destruction.
        next: usize,
        /// Exceptional continuation.
        unwind: Unwind,
    },
    /// Runtime check; the memory proof must establish the normal condition.
    Assert {
        /// Executable condition.
        condition: Operand,
        /// Expected value on the normal edge.
        expected: bool,
        /// Normal continuation.
        next: usize,
        /// Failure continuation.
        unwind: Unwind,
    },
    /// Transfer the return slot to the caller; no implicit deallocation of it.
    Return,
    /// Continue/terminate an unwind already represented by an incoming edge.
    Unwind,
    /// Compiler-unreachable execution; not a user-written assumption.
    Unreachable,
    /// An unsupported control effect. Consumers must fail closed.
    Unsupported,
}

/// A basic block contains ordered statements and exactly one terminator.
#[derive(Clone, Debug)]
pub struct Block {
    /// Statements paired with their executable source locations.
    pub statements: Vec<(Span, Statement)>,
    /// Source location of the control/drop/call event.
    pub span: Span,
    /// The block's final executable effect and outgoing edges.
    pub terminator: Terminator,
    /// Whether the compiler designates this as an unwind cleanup block.
    pub cleanup: bool,
}

/// A source binding's exact compiler place and checked execution mode.
#[derive(Clone, Debug)]
pub struct SourceBinding {
    /// Place matched by source identity, including hygienic binding spans.
    pub place: Place,
    /// Supplied by Verus mode checking. Unknown modes cannot root runtime facts.
    /// Proof bindings are retained for later checked protocol certificates; they
    /// are neither runtime storage nor native mutex acquisition evidence.
    pub mode: Option<Mode>,
}

/// Drop-elaborated compiler evidence for one mode-checked executable function.
/// This is a transport/cleanup graph, not a verified memory summary. Exclusion
/// additionally requires identity resolution, complete allocation coverage,
/// checked helper effects and the global bound proof.
#[derive(Clone, Debug)]
pub struct Graph {
    /// Entry is block zero; preserve back edges instead of unrolling loops.
    pub blocks: Vec<Block>,
    /// Source bindings matched by exact compiler binding spans. Ambiguous or
    /// unavailable matches are omitted and must never be guessed by a consumer.
    pub bindings: HashMap<VarIdent, SourceBinding>,
    /// Number of compiler locals, including return slot zero.
    pub locals: usize,
    /// Compiler argument slots are locals 1 through this count. They may include
    /// proof arguments; source bindings/modes determine executable inputs.
    pub arguments: usize,
}
