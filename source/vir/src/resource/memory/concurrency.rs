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

pub mod invocation;
pub mod sites;

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
    /// Type of the source root before following the compiler's capture path.
    /// A partial capture must not be mistaken for a whole-root move.
    pub source_typ: Typ,
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
    /// Original compiler call kind. Proof erasure may change runtime Copy, but
    /// cannot substitute a different invocation/cleanup graph in this evidence.
    pub kind: crate::ast::ClosureKind,
    /// Source creation site.
    pub span: Span,
    /// Actual post-proof-erasure fields in compiler capture order.
    pub captures: Vec<Capture>,
    /// Whether the source uses a move capture clause; scoped borrowing is outside
    /// the selected worker API even when ordinary closure syntax permits it.
    pub by_move: bool,
    /// Rust's original Copy decision. The accounting layout also derives Copy
    /// from the surviving fields because proof erasure can remove non-Copy state.
    pub copy: bool,
    /// Canonical closure body, retaining actual return and cleanup edges.
    pub body: flow::Graph,
    /// Actual FnOnce adapter for Fn/FnMut closures. Its cleanup destroys the
    /// remaining captured owners after the borrowed body returns.
    pub once_adapter: Option<flow::Graph>,
}

/// A real operation whose ordinary functional translation is an identity.
#[derive(Clone, Debug)]
pub struct ErasedOperation {
    /// Actual compiler-resolved callee, retained for the accounting-only AST.
    pub function: Fun,
    /// Reviewed native operation; currently strong Arc cloning.
    pub operation: Operation,
    /// Actual executable result type, not the identity expression's borrowed type.
    pub result: Typ,
    /// Source call site used for accounting and diagnostics.
    pub span: Span,
    /// Rust's destruction scope for a borrowed temporary receiver. A missing
    /// or unresolved scope cannot justify an early temporary release.
    pub receiver_scope: Option<TemporaryScope>,
}

/// Source boundary selected by rustc's temporary-lifetime rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TemporaryBoundary {
    /// After the executable statement, including all initializer operands.
    Statement,
    /// After the complete expression, including block-local cleanup.
    Expression,
}

/// Compiler lifetime information, awaiting an unambiguous executable VIR site.
#[derive(Clone, Debug)]
pub struct TemporaryScope {
    /// Source node at which rustc ends the temporary's lifetime.
    pub span: Span,
    /// Distinguishes statements from expressions sharing a source location.
    pub boundary: TemporaryBoundary,
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
    /// Native operation site to its resolved destruction boundary in source VIR.
    /// Unresolved/ambiguous boundaries are deliberately absent.
    temporary_scopes: std::collections::BTreeMap<AstId, AstId>,
    /// Index boundaries so sequential expression accounting does not scan every
    /// native operation in the crate at every source expression.
    temporary_scope_ends: std::collections::BTreeSet<AstId>,
    /// Exact native call points for source operations, including identity-erased
    /// calls. An absent binding cannot support an executable memory effect.
    native_sites: std::collections::BTreeMap<AstId, sites::Binding>,
}

impl Evidence {
    /// Record a unique compiler-resolved operation point. This connects source
    /// accounting to executable behavior; it supplies no lifetime or byte bound.
    pub fn record_native_site(&mut self, operation: AstId, binding: sites::Binding) {
        if let Some(previous) = self.native_sites.insert(operation, binding.clone()) {
            assert_eq!(previous, binding, "one executable compiler call point per operation");
        }
    }

    /// Inspect an exact native binding for accounting or compiler diagnostics.
    /// Its presence proves neither event multiplicity nor a memory bound.
    pub fn native_site(&self, operation: AstId) -> Option<&sites::Binding> {
        self.native_sites.get(&operation)
    }

    /// Attach one uniquely resolved executable boundary to its native call.
    pub fn record_temporary_scope(&mut self, operation: AstId, boundary: AstId) {
        if let Some(previous) = self.temporary_scopes.insert(operation, boundary) {
            assert_eq!(previous, boundary, "one compiler destruction scope per operation");
        }
        self.temporary_scope_ends.insert(boundary);
    }

    pub(super) fn temporary_scope(&self, operation: AstId) -> Option<AstId> {
        self.temporary_scopes.get(&operation).copied()
    }

    pub(super) fn ends_temporary_scope(&self, site: AstId) -> bool {
        self.temporary_scope_ends.contains(&site)
    }

    /// Restored identity operations share the surviving source AST ID. Their
    /// nesting order selects the original native site and its cleanup evidence.
    pub(super) fn clone_operation(
        &self,
        expression: &crate::ast::Expr,
    ) -> Option<&ErasedOperation> {
        use crate::ast::*;
        let mut current = expression;
        let mut count = 0usize;
        while current.span.id == expression.span.id {
            let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } = &current.x
            else {
                break;
            };
            if attrs.resource_intrinsic != Some(ResourceIntrinsic::Concurrency(Operation::ArcClone))
            {
                break;
            }
            count += 1;
            let [argument] = args.as_slice() else { return None };
            current = argument;
        }
        let operation =
            self.erased_operations.get(&expression.span.id)?.get(count.checked_sub(1)?)?;
        let ExprX::Call { target: CallTarget::Fun(_, function, _, _, _), .. } = &expression.x
        else {
            return None;
        };
        (operation.function == *function
            && operation.operation == Operation::ArcClone
            && crate::ast_util::types_equal(&operation.result, &expression.typ))
        .then_some(operation)
    }
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

/// Restore executable operations in a private accounting copy. The functional
/// VIR still represents Arc cloning as logical identity; changing that AST would
/// change Verus's established functional/erasure semantics. No restored call is
/// exported or used as a logical assumption.
pub(super) fn accounting_body(
    function: &crate::ast::Function,
    evidence: &Evidence,
) -> Result<crate::ast::Function, crate::ast::VirErr> {
    use std::sync::Arc;
    let Some(body) = &function.x.body else { return Ok(function.clone()) };
    if evidence.erased_operations.is_empty() {
        return Ok(function.clone());
    }
    let body = accounting_expression(body, evidence)?;
    let mut function = function.clone();
    Arc::make_mut(&mut function).x.body = Some(body);
    Ok(function)
}

/// Restore executable native effects in one original functional expression.
/// Accounting expressions already passed through this bridge must not be restored again.
pub(super) fn accounting_expression(
    expression: &crate::ast::Expr,
    evidence: &Evidence,
) -> Result<crate::ast::Expr, crate::ast::VirErr> {
    use crate::ast::*;
    use std::sync::Arc;
    crate::ast_visitor::map_expr_visitor(expression, &|expr| {
        let mut restored = expr.clone();
        if let Some(operations) = evidence.erased_operations.get(&expr.span.id) {
            for operation in operations {
                if operation.operation != Operation::ArcClone {
                    return Err(super::model::unsupported(
                        &operation.span,
                        "an unmodeled executable identity operation",
                    ));
                }
                restored = SpannedTyped::new(
                    // Proof instrumentation must attach to an expression that
                    // still exists in functional VIR. Detailed native call
                    // locations remain in compiler evidence; creating a new
                    // AST ID here would strand the generated assertions.
                    &expr.span,
                    &operation.result,
                    ExprX::Call {
                        target: CallTarget::Fun(
                            CallTargetKind::Static,
                            operation.function.clone(),
                            Arc::new(vec![]),
                            Arc::new(vec![]),
                            CallTargetAttrs {
                                autospec: AutospecUsage::Final,
                                const_var: false,
                                assume_external_allowed: false,
                                resource_intrinsic: Some(ResourceIntrinsic::Concurrency(
                                    operation.operation,
                                )),
                            },
                        ),
                        args: Arc::new(vec![restored]),
                        post_args: None,
                        body: None,
                    },
                );
            }
        }
        Ok(restored)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use std::sync::Arc;

    #[test]
    fn accounting_restores_all_identity_operations_without_mutating_functional_vir() {
        let original_span = Span {
            raw_span: Arc::new(()),
            id: 10,
            data: Arc::new([]),
            as_string: "logical identity".into(),
        };
        let original_type = Arc::new(TypX::Bool);
        let original =
            SpannedTyped::new(&original_span, &original_type, ExprX::Const(Constant::Bool(true)));
        let mut evidence = Evidence::default();
        let result = Arc::new(TypX::Int(IntRange::U(64)));
        evidence.erased_operations.insert(
            original_span.id,
            [11, 12]
                .map(|id| {
                    let mut site = original_span.clone();
                    site.id = id;
                    ErasedOperation {
                        function: crate::fun!(CrateId::Alloc => "sync"; "clone"),
                        operation: Operation::ArcClone,
                        result: result.clone(),
                        span: site,
                        receiver_scope: None,
                    }
                })
                .to_vec(),
        );
        let restored = accounting_expression(&original, &evidence).unwrap();
        assert!(matches!(original.x, ExprX::Const(_)));
        assert!(crate::ast_util::types_equal(&original.typ, &original_type));
        let ExprX::Call { args, .. } = &restored.x else { panic!("outer clone") };
        assert_eq!(restored.span.id, original_span.id);
        assert!(crate::ast_util::types_equal(&restored.typ, &result));
        let ExprX::Call { args: inner, .. } = &args[0].x else { panic!("inner clone") };
        assert_eq!(args[0].span.id, original_span.id);
        assert!(matches!(inner[0].x, ExprX::Const(Constant::Bool(true))));
        assert_eq!(inner[0].span.id, original.span.id);
        assert!(crate::ast_util::types_equal(&inner[0].typ, &original_type));
    }
}
