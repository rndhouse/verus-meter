//! Native receiver temporaries end at compiler-selected source boundaries.
//!
//! These are real owned values, not references manufactured by VIR lowering.
//! Nested expressions sharing one identity-erased source site finish only at
//! the outermost evaluation of that site. Exit edges retain their own storage.

use super::{analysis::Analysis, lifetime::Storage, model::unsupported};
use crate::{
    ast::VirErr,
    messages::{AstId, Span},
};

#[derive(Clone)]
pub(super) struct Temporary {
    scope: AstId,
    span: Span,
    storage: Storage,
}

pub(super) fn compatible(left: &[Temporary], right: &[Temporary]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            left.scope == right.scope && left.storage.compatible(&right.storage)
        })
}

pub(super) struct Evaluation {
    site: AstId,
    first_exit: usize,
}

impl Analysis<'_> {
    pub(super) fn enter_temporary_scope(&mut self, site: AstId) -> Option<Evaluation> {
        if !self.concurrency.ends_temporary_scope(site) {
            return None;
        }
        *self.evaluations.entry(site).or_default() += 1;
        Some(Evaluation { site, first_exit: self.flow.exits.len() })
    }

    pub(super) fn finish_temporary_scope(&mut self, evaluation: Option<Evaluation>) {
        let Some(Evaluation { site, first_exit }) = evaluation else { return };
        let depth = self.evaluations.get_mut(&site).expect("an active source evaluation");
        *depth -= 1;
        if *depth != 0 {
            return;
        }
        self.evaluations.remove(&site);
        self.cleanup_edges(first_exit, |analysis, _| {
            let mut remaining = Vec::new();
            while let Some(temporary) = analysis.heap.temporaries.pop() {
                if temporary.scope == site {
                    if let Some(owner) = temporary.storage.owner {
                        analysis.release_owner(owner, &temporary.span);
                    }
                    analysis.release_value(temporary.storage.value, &temporary.span);
                } else {
                    remaining.push(temporary);
                }
            }
            remaining.reverse();
            analysis.heap.temporaries = remaining;
        });
    }

    /// Retain the owned receiver independently of the cloned result. A missing
    /// active boundary cannot be replaced by an assumed end-of-call lifetime.
    pub(super) fn retain_temporary(
        &mut self,
        operation: AstId,
        span: &Span,
        storage: Storage,
    ) -> Result<(), VirErr> {
        let scope = self.concurrency.temporary_scope(operation).ok_or_else(|| {
            unsupported(span, "a receiver temporary without an exact compiler destruction scope")
        })?;
        if !self.evaluations.contains_key(&scope) {
            return Err(unsupported(
                span,
                "a receiver temporary outside its accounted source scope",
            ));
        }
        self.heap.temporaries.push(Temporary { scope, span: span.clone(), storage });
        Ok(())
    }
}
