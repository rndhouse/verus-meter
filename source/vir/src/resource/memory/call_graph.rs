//! Synchronous and worker dependencies share cycle checking, not call composition.

use super::{execution, model::unsupported};
use crate::ast::*;
use crate::ast_visitor::{AstVisitor, NoScoper, Walk};
use crate::messages::{Span, error};
use crate::resolution_inference::ResolutionInfo;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Checked executable dependencies used before publishing any function summaries.
pub(super) struct CallGraph {
    // Per-function call sites in source order, keeping cycle diagnostics deterministic.
    edges: HashMap<Fun, Vec<(Fun, Span)>>,
    /// Publication starts a child that may run immediately. These dependencies
    /// participate in recursion checks but never in synchronous call validation.
    spawns: HashMap<Fun, Vec<(Fun, Span)>>,
    /// Diagnostic locations for both named functions and concrete worker bodies.
    spans: HashMap<Fun, Span>,
}

struct Collector<'a> {
    // Local declarations identify contracted callees and executable parameters.
    functions: &'a HashMap<Fun, Function>,
    // Resolved local modes distinguish ghost declarations from runtime work.
    modes: &'a HashMap<VarIdent, Mode>,
    // Calls found in this body, retaining their original diagnostic spans.
    edges: Vec<(Fun, Span)>,
    /// Compiler identities of the concrete executable closures in this crate.
    closures: &'a HashMap<usize, super::concurrency::Closure>,
    /// Asynchronous publications found in this body.
    spawns: Vec<(Fun, Span)>,
}

impl AstVisitor<Walk, VirErr, NoScoper> for Collector<'_> {
    /// Collect calls in executed expressions and arguments, excluding specifications.
    fn visit_expr(&mut self, expr: &Expr) -> Result<(), VirErr> {
        if execution::ignored_expression(expr) {
            return Ok(());
        }
        if matches!(expr.x, ExprX::NonSpecClosure { .. }) {
            // Creation transfers captures; it does not execute the body. Worker
            // publication and the worker's own dependencies are separate edges.
            return Ok(());
        }
        if let ExprX::OpenInvariant(_, _, body, _) = &expr.x {
            return self.visit_expr(body);
        }
        // Invariants and decreases are specifications, not executable loop work.
        if let ExprX::Loop { cond, body, .. } = &expr.x {
            if let Some(cond) = cond {
                self.visit_expr(cond)?;
            }
            return self.visit_expr(body);
        }
        if let ExprX::Call {
            target: CallTarget::Fun(CallTargetKind::Static, target, _, _, attrs),
            args,
            ..
        } = &expr.x
        {
            if let Some(ResourceIntrinsic::Concurrency(operation)) = attrs.resource_intrinsic
                && operation.spawns()
            {
                let closure = args
                    .first()
                    .and_then(|arg| match &*arg.typ {
                        TypX::AnonymousClosure(_, _, _, id) => self.closures.get(id),
                        _ => None,
                    })
                    .ok_or_else(|| {
                        unsupported(
                            &expr.span,
                            "worker publication without a concrete compiler-derived closure",
                        )
                    })?;
                self.spawns.push((closure.function.clone(), expr.span.clone()));
            }
            if attrs.resource_intrinsic.is_none()
                && self.functions.get(target).is_some_and(|f| f.x.attrs.resource_contract.is_some())
            {
                self.edges.push((target.clone(), expr.span.clone()));
            }
            // Only executable arguments run; ghost parameters do not add edges.
            if let Some(callee) = self.functions.get(target) {
                for (arg, param) in args.iter().zip(callee.x.params.iter()) {
                    if param.x.mode == Mode::Exec {
                        self.visit_expr(arg)?;
                    }
                }
                return Ok(());
            }
        }
        self.visit_expr_rec(expr)
    }

    /// Prune erased declarations before descending into their initializers.
    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<(), VirErr> {
        if execution::ignored_statement(stmt, self.modes) {
            Ok(())
        } else {
            self.visit_stmt_rec(stmt)
        }
    }

    /// Follow temporaries embedded in places, including calls producing aggregates.
    fn visit_place(&mut self, place: &Place) -> Result<(), VirErr> {
        self.visit_place_rec(place)
    }

    /// Pattern bindings contain no executable work.
    fn visit_pattern(&mut self, _: &Pattern) -> Result<(), VirErr> {
        Ok(())
    }

    /// Type metadata does not introduce executable call edges.
    fn visit_typ(&mut self, _: &Typ) -> Result<(), VirErr> {
        Ok(())
    }
}

impl CallGraph {
    pub(super) fn publishes_workers(&self, function: &Function) -> bool {
        self.spawns.get(&function.x.name).is_some_and(|sites| !sites.is_empty())
    }
    /// Discover the checked call edges using the same execution boundaries as accounting.
    pub(super) fn new(
        functions: &HashMap<Fun, Function>,
        modes: &HashMap<Fun, Arc<ResolutionInfo>>,
        concurrency: &super::concurrency::Evidence,
    ) -> Result<Self, VirErr> {
        let mut edges = HashMap::new();
        let mut spawns = HashMap::new();
        let mut spans = HashMap::new();
        let empty = HashMap::new();
        for (name, function) in functions {
            let var_modes = modes.get(name).map(|m| &m.var_modes).unwrap_or(&empty);
            let mut collector = Collector {
                functions,
                modes: var_modes,
                edges: Vec::new(),
                closures: &concurrency.closures,
                spawns: Vec::new(),
            };
            if function.x.attrs.resource_contract.is_some() {
                if let Some(body) = &function.x.body {
                    collector.visit_expr(body)?;
                    // Register bodies independently of creation/execution. Only
                    // publication edges make them reachable in the dependency
                    // traversal. Nested workers keep the enclosing mode map.
                    crate::ast_visitor::expr_visitor_check(body, &mut |_, expr| {
                        if let ExprX::NonSpecClosure { body, proof_fn_modes: None, .. } = &expr.x
                            && let TypX::AnonymousClosure(_, _, _, id) = &*expr.typ
                            && let Some(closure) = concurrency.closures.get(id)
                        {
                            let mut worker = Collector {
                                functions,
                                modes: var_modes,
                                edges: Vec::new(),
                                closures: &concurrency.closures,
                                spawns: Vec::new(),
                            };
                            worker.visit_expr(body)?;
                            edges.insert(closure.function.clone(), worker.edges);
                            spawns.insert(closure.function.clone(), worker.spawns);
                            spans.insert(closure.function.clone(), closure.span.clone());
                        }
                        Ok::<(), VirErr>(())
                    })?;
                }
            }
            edges.insert(name.clone(), collector.edges);
            spawns.insert(name.clone(), collector.spawns);
            spans.insert(name.clone(), function.span.clone());
        }
        Ok(Self { edges, spawns, spans })
    }

    /// Visit callees first; a back edge rejects recursion at the originating call.
    pub(super) fn order(&self, functions: &[Function]) -> Result<Vec<Function>, VirErr> {
        // Emit a callee before its callers, or diagnose the edge closing a cycle.
        fn visit(
            graph: &CallGraph,
            name: &Fun,
            functions: &HashMap<Fun, Function>,
            active: &mut HashSet<Fun>,
            done: &mut HashSet<Fun>,
            ordered: &mut Vec<Function>,
        ) -> Result<(), VirErr> {
            if done.contains(name) {
                return Ok(());
            }
            active.insert(name.clone());
            for (callee, span) in graph.edges[name].iter().chain(&graph.spawns[name]) {
                if active.contains(callee) {
                    return Err(unsupported(
                        span,
                        "recursive memory contracts (including mutual recursion)",
                    )
                    .secondary_span(&graph.spans[callee]));
                }
                visit(graph, callee, functions, active, done, ordered)?;
            }
            active.remove(name);
            done.insert(name.clone());
            if let Some(function) = functions.get(name) {
                ordered.push(function.clone());
            }
            Ok(())
        }
        let map = functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();
        let mut ordered = Vec::new();
        let mut active = HashSet::new();
        let mut done = HashSet::new();
        for function in functions {
            visit(self, &function.x.name, &map, &mut active, &mut done, &mut ordered)?;
        }
        Ok(ordered)
    }

    /// Fail closed if a future lowering makes discovery miss an accounted call.
    /// Both ordering and recursion checks must cover every call the model uses.
    pub(super) fn validate_calls(
        &self,
        function: &Function,
        calls: &[(Fun, Span)],
    ) -> Result<(), VirErr> {
        let known: HashSet<_> =
            self.edges[&function.x.name].iter().map(|(callee, site)| (callee, site.id)).collect();
        for (callee, span) in calls {
            if !known.contains(&(callee, span.id)) {
                return Err(error(
                    span,
                    "memory accounting reached a call absent from its executable call graph",
                ));
            }
        }
        Ok(())
    }
}
