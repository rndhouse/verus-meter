//! One executable-call graph supplies ordering, cycle checks, and traversal validation.

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
}

struct Collector<'a> {
    // Local declarations identify contracted callees and executable parameters.
    functions: &'a HashMap<Fun, Function>,
    // Resolved local modes distinguish ghost declarations from runtime work.
    modes: &'a HashMap<VarIdent, Mode>,
    // Calls found in this body, retaining their original diagnostic spans.
    edges: Vec<(Fun, Span)>,
}

impl AstVisitor<Walk, VirErr, NoScoper> for Collector<'_> {
    /// Collect calls in executed expressions and arguments, excluding specifications.
    fn visit_expr(&mut self, expr: &Expr) -> Result<(), VirErr> {
        if execution::ignored_expression(expr) {
            return Ok(());
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
    /// Discover the checked call edges using the same execution boundaries as accounting.
    pub(super) fn new(
        functions: &HashMap<Fun, Function>,
        modes: &HashMap<Fun, Arc<ResolutionInfo>>,
    ) -> Result<Self, VirErr> {
        let mut edges = HashMap::new();
        let empty = HashMap::new();
        for (name, function) in functions {
            let mut collector = Collector {
                functions,
                modes: modes.get(name).map(|m| &m.var_modes).unwrap_or(&empty),
                edges: Vec::new(),
            };
            if function.x.attrs.resource_contract.is_some() {
                if let Some(body) = &function.x.body {
                    collector.visit_expr(body)?;
                }
            }
            edges.insert(name.clone(), collector.edges);
        }
        Ok(Self { edges })
    }

    /// Visit callees first; a back edge rejects recursion at the originating call.
    pub(super) fn order(&self, functions: &[Function]) -> Result<Vec<Function>, VirErr> {
        // Emit a callee before its callers, or diagnose the edge closing a cycle.
        fn visit(
            graph: &CallGraph,
            function: &Function,
            functions: &HashMap<Fun, Function>,
            active: &mut HashSet<Fun>,
            done: &mut HashSet<Fun>,
            ordered: &mut Vec<Function>,
        ) -> Result<(), VirErr> {
            let name = &function.x.name;
            if done.contains(name) {
                return Ok(());
            }
            active.insert(name.clone());
            for (callee, span) in &graph.edges[name] {
                if active.contains(callee) {
                    return Err(unsupported(
                        span,
                        "recursive memory contracts (including mutual recursion)",
                    )
                    .secondary_span(&functions[callee].span));
                }
                visit(graph, &functions[callee], functions, active, done, ordered)?;
            }
            active.remove(name);
            done.insert(name.clone());
            ordered.push(function.clone());
            Ok(())
        }
        let map = functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();
        let mut ordered = Vec::new();
        let mut active = HashSet::new();
        let mut done = HashSet::new();
        for function in functions {
            visit(self, function, &map, &mut active, &mut done, &mut ordered)?;
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
