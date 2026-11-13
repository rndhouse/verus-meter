//! Lexical proof scopes and reuse of graph visits, lemma facts, and range proofs.
//!
//! Only ancestor and current-scope facts can satisfy requests. Keep cached
//! expressions alive while their pointer identities are used as keys.

use super::super::{expr, simplify};
use crate::ast::*;
use crate::messages::Span;
use std::collections::HashMap;
use std::sync::Arc;

/// Facts established for shared expression nodes in this lexical proof scope.
/// Ancestor facts are available in a branch; branch-local facts cannot escape
/// to its sibling or parent. Quantified builder proofs start a fresh emitter.
pub(super) struct ForestProofs {
    /// Retain each expression while its pointer identity is cached. Multiple
    /// roots may contain temporary nodes whose addresses would otherwise recycle.
    /// The root scope remains present until the emitter is discarded.
    scopes: Vec<Scope>,
    /// Deterministic traversal work used by sharing regressions and measurements.
    #[cfg(test)]
    pub(super) work: Work,
}

#[cfg(test)]
#[derive(Default)]
pub(super) struct Work {
    /// Structural range helper bodies evaluated after cache lookup.
    pub(super) blocks: usize,
    /// Runtime-filter helper bodies evaluated after cache lookup.
    pub(super) retentions: usize,
}

/// Graph visits and pure lemma facts established under one set of assumptions.
#[derive(Default)]
struct Scope {
    /// Shared graph nodes already visited under these assumptions.
    nodes: HashMap<usize, Expr>,
    /// Pure lemma calls already established in this scope, grouped by callee.
    lemmas: HashMap<Fun, Vec<Exprs>>,
    /// Completed structural range proofs for a forest and an exact width.
    blocks: BoundProofs,
    /// Completed runtime-filter traversals for a forest and an exact cut length.
    retentions: BoundProofs,
}

/// A traversal can be reused only for the same forest and scalar bound.
/// Retaining the forest keeps pointer keys valid across temporary input roots.
#[derive(Default)]
struct BoundProofs {
    /// Forest identity, its retained expression, and completed traversal bounds.
    values: HashMap<usize, (Expr, Vec<Expr>)>,
}

impl BoundProofs {
    fn contains(&self, value: &Expr, bound: &Expr) -> bool {
        self.values.get(&(Arc::as_ptr(value) as usize)).is_some_and(|(_, bounds)| {
            bounds.iter().any(|old| simplify::same_expression(old, bound))
        })
    }

    fn insert(&mut self, value: &Expr, bound: &Expr) {
        self.values
            .entry(Arc::as_ptr(value) as usize)
            .or_insert_with(|| (value.clone(), Vec::new()))
            .1
            .push(bound.clone());
    }
}

impl ForestProofs {
    /// Start an independent proof query with an unconditional root scope.
    pub(super) fn new() -> Self {
        Self {
            scopes: vec![Scope::default()],
            #[cfg(test)]
            work: Work::default(),
        }
    }

    /// Establish branch-local facts while retaining access to ancestor facts.
    pub(super) fn branch(&mut self, span: &Span, value: &Expr) -> Result<Vec<Stmt>, VirErr> {
        self.scopes.push(Scope::default());
        let mut proofs = Vec::new();
        let result = self.forest(span, value, &mut proofs);
        self.scopes.pop();
        result?;
        Ok(proofs)
    }

    /// Generated metadata lemmas are pure: identical arguments establish the
    /// same facts again. Compare within this branch and its ancestors only.
    pub(super) fn lemma(
        &mut self,
        span: &Span,
        name: &str,
        args: Vec<Expr>,
        proofs: &mut Vec<Stmt>,
    ) {
        let function = expr::function(name);
        if self.scopes.iter().any(|scope| {
            scope.lemmas.get(&function).is_some_and(|previous| {
                previous.iter().any(|old| {
                    old.len() == args.len()
                        && old.iter().zip(&args).all(|(a, b)| simplify::same_expression(a, b))
                })
            })
        }) {
            return;
        }
        self.scopes
            .last_mut()
            .unwrap()
            .lemmas
            .entry(function)
            .or_default()
            .push(Arc::new(args.clone()));
        proofs.push(expr::lemma(span, name, args));
    }

    /// Visit a shared graph node once under the current assumptions.
    pub(super) fn visit(&mut self, value: &Expr) -> bool {
        let key = Arc::as_ptr(value) as usize;
        if self.scopes.iter().any(|scope| scope.nodes.contains_key(&key)) {
            return false;
        }
        self.scopes.last_mut().unwrap().nodes.insert(key, value.clone());
        true
    }

    /// Check ancestor and local block facts before doing structural proof work.
    pub(super) fn needs_block(&mut self, value: &Expr, width: &Expr) -> bool {
        if self.scopes.iter().any(|scope| scope.blocks.contains(value, width)) {
            return false;
        }
        #[cfg(test)]
        {
            self.work.blocks += 1;
        }
        true
    }

    /// Publish a block fact only after its structural proof has succeeded.
    pub(super) fn complete_block(&mut self, value: &Expr, width: &Expr) {
        self.scopes.last_mut().unwrap().blocks.insert(value, width);
    }

    /// Check retention facts independently of structural block facts.
    pub(super) fn needs_retention(&mut self, memory: &Expr, length: &Expr) -> bool {
        if self.scopes.iter().any(|scope| scope.retentions.contains(memory, length)) {
            return false;
        }
        #[cfg(test)]
        {
            self.work.retentions += 1;
        }
        true
    }

    /// Publish completed runtime-filter work in the current proof scope.
    pub(super) fn complete_retention(&mut self, memory: &Expr, length: &Expr) {
        self.scopes.last_mut().unwrap().retentions.insert(memory, length);
    }
}
