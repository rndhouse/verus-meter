//! Worker and shared-owner effects, distinct from synchronous function calls.
//!
//! Reviewed Rust/vstd operations describe publication, waiting and strong-owner
//! lifetimes. They do not provide a worker byte bound or turn Send/Sync into
//! exclusion. User function specifications cannot create these effects.

use super::synchronization::flow;
use crate::ast::{Fun, Typ, VarIdent};
use crate::messages::{AstId, Span};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use vir_macros::ToDebugSNode;

/// Capture transport selected by Rust's post-erasure capture analysis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaptureMode {
    /// New inline storage, retaining any existing shared identity.
    Copy,
    /// Transfer owned storage without duplicating descendants.
    Move,
    /// A view of an existing object; no new owner or acquisition.
    Borrow,
}

/// One actual executable capture, independent of synthetic lifetime-check fields.
#[derive(Clone, Debug)]
pub struct Capture {
    /// Canonical source binding in the enclosing function/worker.
    pub source: VarIdent,
    /// Fixed path from that binding to the captured object.
    pub projection: Vec<flow::Projection>,
    /// Runtime field type, including reference decoration for borrowed captures.
    pub typ: Typ,
    /// Whether construction copies, moves or borrows this object.
    pub mode: CaptureMode,
    /// Corresponding place in the lifetime-check closure body. A missing bridge
    /// cannot support a synchronization-containment proof.
    pub body_place: Option<flow::Place>,
}

/// Executable closure storage and body evidence from mode checking and rustc.
#[derive(Clone, Debug)]
pub struct Closure {
    /// Local closure type identity used by VIR's AnonymousClosure type.
    pub id: usize,
    /// Resolved body identity, distinct from the function creating the closure.
    pub function: Fun,
    /// Source creation site.
    pub span: Span,
    /// Actual post-proof-erasure fields in compiler capture order.
    pub captures: Vec<Capture>,
    /// Whether the source uses a move capture clause; scoped borrowing is outside
    /// the selected worker API even when ordinary closure syntax permits it.
    pub by_move: bool,
    /// Canonical closure body, retaining actual return and cleanup edges.
    pub body: flow::Graph,
    /// Actual FnOnce adapter for Fn/FnMut closures. Its cleanup destroys the
    /// remaining captured owners after the borrowed body returns.
    pub once_adapter: Option<flow::Graph>,
}

/// A real operation whose ordinary functional translation is an identity.
#[derive(Clone, Debug)]
pub struct ErasedOperation {
    /// Reviewed native operation; currently strong Arc cloning.
    pub operation: Operation,
    /// Actual executable result type, not the identity expression's borrowed type.
    pub result: Typ,
    /// Source call site used for accounting and diagnostics.
    pub span: Span,
}

/// Compiler-owned evidence. These records cannot establish a memory theorem
/// without ownership/lifetime validation and the later global bound proof.
#[derive(Clone, Debug, Default)]
pub struct Evidence {
    /// Concrete closure fields/body keyed by compiler type identity.
    pub closures: HashMap<usize, Closure>,
    /// Logical identity expressions still correspond to executable operations.
    /// Several nested identity translations can share one surviving expression;
    /// preserve every executable operation in evaluation order.
    pub erased_operations: HashMap<AstId, Vec<ErasedOperation>>,
}

/// Inline closure field storage under the existing source model. Captured heap
/// descendants and shared backing retain their own ownership identities and are
/// deliberately excluded from this inline quantity.
pub fn capture_storage(
    closure: &Closure,
    datatypes: &[crate::ast::Datatype],
    global_allocator: Option<crate::ast::Dt>,
    vector: Option<crate::ast::Dt>,
    option: Option<crate::ast::Dt>,
    types: &super::synchronization::LibraryTypes,
) -> Result<u64, crate::ast::VirErr> {
    let layouts = super::layout::Layouts::new(datatypes, global_allocator, vector, option)
        .with_synchronization_types(types);
    closure.captures.iter().try_fold(0u64, |total, capture| {
        total.checked_add(layouts.size(&capture.typ, &closure.span)?).ok_or_else(|| {
            super::model::unsupported(&closure.span, "closure storage exceeding u64")
        })
    })
}

/// Compiler-identified operations in the supported concurrent execution model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, ToDebugSNode)]
pub enum Operation {
    /// Allocate a fresh backing object and its first strong handle.
    ArcNew,
    /// Create a fresh handle to an existing backing object, without cloning it.
    ArcClone,
    /// Borrow a shared payload; this neither creates a handle nor copies storage.
    ArcBorrow,
    /// Consume a strong handle; only the last strong destruction reclaims backing.
    ArcDrop,
    /// Publish a Rust worker. It can run before the call returns.
    StdSpawn,
    /// Consume a Rust join handle, waiting for completion before transferring its result.
    StdJoin,
    /// Reviewed vstd wrapper with the same publication/storage semantics.
    VstdSpawn,
    /// Reviewed vstd wrapper with the same waiting/result-transfer semantics.
    VstdJoin,
}

impl Operation {
    /// Spawning is asynchronous; do not compose it as a completed helper call.
    pub fn spawns(self) -> bool {
        matches!(self, Self::StdSpawn | Self::VstdSpawn)
    }

    /// Joining waits without releasing the caller's frame or retained storage.
    pub fn joins(self) -> bool {
        matches!(self, Self::StdJoin | Self::VstdJoin)
    }
}
