//! Source/native operation correspondence, retaining the containing control
//! graph. A static call site is not a dynamic worker or a population count.
//! Primitive contracts supply publication/wait boundaries inside opaque calls;
//! binding a spawn call never makes its child a completed synchronous helper.

use super::{Evidence, Operation};
use crate::{
    ast::*,
    ast_visitor::{AstVisitor, NoScoper, Walk},
    messages::{AstId, Span},
};
use std::collections::{BTreeSet, HashMap};

/// A repeated source region whose dynamic visit must be bound at execution.
/// The function/closure scope namespaces `site`; these are binder requirements,
/// not iteration ordinals or proofs of a particular number of visits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Iteration {
    /// Original loop identity, retained by memory's for-loop preparation.
    pub site: AstId,
    /// Conditions and successful bodies have different visit populations.
    pub part: LoopPart,
}

/// A condition can execute once more than its body, or exit without entering it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoopPart {
    /// Executable condition, including effects before a false result.
    Head,
    /// Executable body, including exits before a back edge.
    Body,
}

/// One executable source operation before functional identity erasure.
#[derive(Clone)]
pub struct Call<T = Operation> {
    /// Native call identity; erased calls can share an accounting anchor.
    pub id: AstId,
    /// Source expression retained for generated proof obligations.
    pub anchor: AstId,
    /// Exact original native call span, including hygiene.
    pub span: Span,
    /// Actual function/closure body whose graph contains the call.
    pub scope: Fun,
    /// Resolved primitive, independent of source spelling or specifications.
    pub operation: T,
    /// Enclosing local loop regions, from outermost to innermost. A closure
    /// body starts a new local context; its parent's visits belong to its
    /// invocation identity, not to the child's local iteration counters.
    pub iterations: Vec<Iteration>,
}

/// An exact compiler point, not an assumed operation count or completion fact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding<T = Operation> {
    /// Surviving source expression where accounting obligations attach.
    pub anchor: AstId,
    /// Function-local graph namespace, distinct from a thread occurrence.
    pub scope: Fun,
    /// Terminator point in the original drop-elaborated control graph.
    pub point: super::super::synchronization::flow::Point,
    /// Primitive executed at that point.
    pub operation: T,
    /// Local repeated-region binders required by this source operation.
    pub iterations: Vec<Iteration>,
}

/// Source sites collected together under one control-flow and erasure policy.
#[derive(Default)]
pub struct Calls {
    /// Thread and shared-ownership operations.
    pub concurrent: Vec<Call>,
    /// Native synchronization operations, with the same exact source namespace.
    pub synchronization: Vec<Call<super::super::synchronization::Operation>>,
}

/// Collect runtime operations using the same erasure boundaries as accounting.
/// Body discovery may include latent closures; admission validates only code
/// actually executed in the scope being checked.
pub fn calls(
    function: &Function,
    modes: &crate::resolution_inference::ResolutionInfo,
    functions: &[Function],
    evidence: &Evidence,
    include_closure_bodies: bool,
) -> Vec<Call> {
    collect(function, &modes.var_modes, functions, evidence, include_closure_bodies).concurrent
}

/// Include all executable primitive calls when resolving their compiler points.
pub fn all_calls(
    function: &Function,
    modes: &crate::resolution_inference::ResolutionInfo,
    functions: &[Function],
    evidence: &Evidence,
) -> Calls {
    collect(function, &modes.var_modes, functions, evidence, true)
}

fn collect(
    function: &Function,
    modes: &HashMap<VarIdent, Mode>,
    functions: &[Function],
    evidence: &Evidence,
    include_closure_bodies: bool,
) -> Calls {
    struct Collect<'a> {
        modes: &'a HashMap<VarIdent, Mode>,
        functions: &'a [Function],
        evidence: &'a Evidence,
        scope: Fun,
        iterations: Vec<Iteration>,
        include_closures: bool,
        seen: BTreeSet<AstId>,
        calls: Calls,
    }
    impl Collect<'_> {
        fn record(&mut self, id: AstId, anchor: AstId, span: &Span, operation: Operation) {
            if self.seen.insert(id) {
                self.calls.concurrent.push(Call {
                    id,
                    anchor,
                    span: span.clone(),
                    scope: self.scope.clone(),
                    operation,
                    iterations: self.iterations.clone(),
                });
            }
        }
    }
    impl AstVisitor<Walk, (), NoScoper> for Collect<'_> {
        fn visit_expr(&mut self, expression: &Expr) -> Result<(), ()> {
            if super::super::execution::ignored_expression(expression) {
                return Ok(());
            }
            let evidence = self.evidence;
            if let Some(operations) = evidence.erased_operations.get(&expression.span.id) {
                for operation in operations {
                    self.record(
                        operation.span.id,
                        expression.span.id,
                        &operation.span,
                        operation.operation,
                    );
                }
            }
            if let ExprX::NonSpecClosure { body, proof_fn_modes, .. } = &expression.x {
                if self.include_closures
                    && proof_fn_modes.is_none()
                    && let TypX::AnonymousClosure(_, _, _, id) = &*expression.typ
                    && let Some(closure) = self.evidence.closures.get(id)
                {
                    let previous = std::mem::replace(&mut self.scope, closure.function.clone());
                    let iterations = std::mem::take(&mut self.iterations);
                    self.visit_expr(body)?;
                    self.scope = previous;
                    self.iterations = iterations;
                }
                return Ok(());
            }
            if let ExprX::Loop { cond, body, source, .. } = &expression.x {
                let repeated = matches!(source, LoopSource::Loop);
                if repeated {
                    self.iterations
                        .push(Iteration { site: expression.span.id, part: LoopPart::Head });
                }
                if let Some(condition) = cond {
                    self.visit_expr(condition)?;
                }
                if repeated {
                    self.iterations.last_mut().unwrap().part = LoopPart::Body;
                }
                self.visit_expr(body)?;
                if repeated {
                    self.iterations.pop();
                }
                return Ok(());
            }
            if let ExprX::Call { target: CallTarget::Fun(_, target, _, _, attrs), args, .. } =
                &expression.x
            {
                if let Some(ResourceIntrinsic::Concurrency(operation)) = attrs.resource_intrinsic {
                    self.record(
                        expression.span.id,
                        expression.span.id,
                        &expression.span,
                        operation,
                    );
                }
                if let Some(ResourceIntrinsic::Synchronization(operation)) =
                    attrs.resource_intrinsic
                    && self.seen.insert(expression.span.id)
                {
                    self.calls.synchronization.push(Call {
                        id: expression.span.id,
                        anchor: expression.span.id,
                        scope: self.scope.clone(),
                        span: expression.span.clone(),
                        iterations: self.iterations.clone(),
                        operation,
                    });
                }
                if let Some(callee) = self.functions.iter().find(|callee| callee.x.name == *target)
                {
                    if callee.x.mode != Mode::Exec {
                        return Ok(());
                    }
                    for (argument, parameter) in args.iter().zip(callee.x.params.iter()) {
                        if parameter.x.mode == Mode::Exec {
                            self.visit_expr(argument)?;
                        }
                    }
                    return Ok(());
                }
            }
            self.visit_expr_rec(expression)
        }
        fn visit_stmt(&mut self, statement: &Stmt) -> Result<(), ()> {
            if super::super::execution::ignored_statement(statement, self.modes) {
                Ok(())
            } else {
                self.visit_stmt_rec(statement)
            }
        }
        fn visit_place(&mut self, place: &Place) -> Result<(), ()> {
            self.visit_place_rec(place)
        }
        fn visit_typ(&mut self, _: &Typ) -> Result<(), ()> {
            Ok(())
        }
        fn visit_pattern(&mut self, _: &Pattern) -> Result<(), ()> {
            Ok(())
        }
    }
    let mut collect = Collect {
        modes,
        functions,
        evidence,
        scope: function.x.name.clone(),
        iterations: vec![],
        include_closures: include_closure_bodies,
        seen: BTreeSet::new(),
        calls: Calls::default(),
    };
    if let Some(body) = &function.x.body {
        let _ = collect.visit_expr(body);
    }
    collect.calls
}

pub(in super::super) fn validate(
    function: &Function,
    modes: &HashMap<VarIdent, Mode>,
    functions: &[Function],
    evidence: &super::super::synchronization::CompilerEvidence,
) -> Result<(), VirErr> {
    for call in collect(function, modes, functions, &evidence.concurrency, false).concurrent {
        if !bound(&call, evidence) {
            return Err(super::super::model::unsupported(
                &call.span,
                "an executable concurrent effect without an exact compiler call binding",
            ));
        }
    }
    Ok(())
}

/// Validate only closure bodies that the memory pass actually entered. Latent
/// closures remain construction effects, with no executable body obligations.
pub(in super::super) fn validate_workers(
    function: &Function,
    modes: &HashMap<VarIdent, Mode>,
    functions: &[Function],
    evidence: &super::super::synchronization::CompilerEvidence,
    definitions: &BTreeSet<usize>,
) -> Result<(), VirErr> {
    let scopes: BTreeSet<_> = definitions
        .iter()
        .filter_map(|id| {
            evidence.concurrency.closures.get(id).map(|closure| closure.function.clone())
        })
        .collect();
    for call in collect(function, modes, functions, &evidence.concurrency, true).concurrent {
        if scopes.contains(&call.scope) && !bound(&call, evidence) {
            return Err(super::super::model::unsupported(
                &call.span,
                "a worker effect without its exact source/native scope binding",
            ));
        }
    }
    Ok(())
}

fn bound(call: &Call, evidence: &super::super::synchronization::CompilerEvidence) -> bool {
    use super::super::synchronization::flow::{Call as NativeCall, Terminator};
    let Some(binding) = evidence.concurrency.native_site(call.id) else { return false };
    if binding.anchor != call.anchor
        || binding.scope != call.scope
        || binding.operation != call.operation
        || binding.iterations != call.iterations
    {
        return false;
    }
    let Some(graph) = evidence.graph(&binding.scope) else { return false };
    let Some(block) = graph.blocks.get(binding.point.block) else { return false };
    binding.point.statement == block.statements.len()
        && matches!(block.terminator, Terminator::Call { call: NativeCall::Concurrent(operation), .. } if operation == call.operation)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resource::memory::synchronization::{CompilerEvidence, flow};
    use std::sync::Arc;

    fn span(id: AstId) -> Span {
        Span { raw_span: Arc::new(()), id, data: Arc::new([]), as_string: "native site".into() }
    }

    fn graph() -> flow::Graph {
        flow::Graph {
            blocks: (0..2)
                .map(|id| flow::Block {
                    statements: vec![],
                    span: span(id),
                    cleanup: false,
                    terminator: flow::Terminator::Call {
                        call: flow::Call::Concurrent(Operation::ArcClone),
                        arguments: vec![],
                        destination: flow::Place { local: 0, projection: vec![] },
                        outcomes: vec![],
                        next: None,
                        unwind: flow::Unwind::Exit,
                    },
                })
                .collect(),
            bindings: HashMap::new(),
            locals: 1,
            arguments: 0,
        }
    }

    #[test]
    fn shared_anchors_preserve_distinct_calls_and_graph_namespaces() {
        let first = crate::fun!(CrateId::Internal => "site_test"; "first");
        let second = crate::fun!(CrateId::Internal => "site_test"; "second");
        let mut evidence = CompilerEvidence::default();
        evidence.cleanup.insert(first.clone(), graph());
        evidence.cleanup.insert(second.clone(), graph());
        let call = Call {
            id: 10,
            anchor: 42,
            span: span(10),
            scope: first.clone(),
            operation: Operation::ArcClone,
            iterations: vec![],
        };
        assert!(!bound(&call, &evidence));
        for (id, block) in [(10, 0), (11, 1)] {
            evidence.concurrency.record_native_site(
                id,
                Binding {
                    anchor: 42,
                    scope: first.clone(),
                    operation: Operation::ArcClone,
                    point: flow::Point { block, statement: 0 },
                    iterations: vec![],
                },
            );
        }
        assert!(bound(&call, &evidence));
        let next = Call { id: 11, ..call.clone() };
        assert!(bound(&next, &evidence));
        assert!(!bound(
            &Call {
                iterations: vec![Iteration { site: 100, part: LoopPart::Body }],
                ..next.clone()
            },
            &evidence
        ));
        // Reusing a block index in another function does not bind this source
        // call. A named helper also cannot impersonate a reviewed native call.
        assert!(!bound(&Call { scope: second, ..next.clone() }, &evidence));
        let flow::Terminator::Call { call: native, .. } =
            &mut evidence.cleanup.get_mut(&first).unwrap().blocks[1].terminator
        else {
            unreachable!()
        };
        *native = flow::Call::Function(crate::fun!(CrateId::Internal => "site_test"; "clone"));
        assert!(!bound(&next, &evidence));
        assert!(bound(&call, &evidence));
    }
}
