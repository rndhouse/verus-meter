//! Ownership transformations shared by local accounting and helper summaries.
//!
//! These rules transform allocation descriptors. Callers schedule snapshots,
//! prove the algebra's preconditions, and account for temporary overlap before
//! releasing displaced storage. The input may be a whole owner or its runtime
//! children; descriptors outside the selected subtree remain in the remainder.

use super::expr;
use crate::ast::*;
use crate::messages::Span;
use crate::resource::memory::{contracts, growth};

/// Selected ownership and the descriptors retained by its parent.
pub(in super::super) struct Partition {
    /// Selected descriptors, relative to the child, preserving the input's view.
    pub(in super::super) selected: Expr,
    /// Retained descriptors, including any sibling reindexing by the operation.
    pub(in super::super) remaining: Expr,
}

/// Detach a child without changing the parent allocation or sibling descriptors.
pub(in super::super) fn detach(span: &Span, memory: Expr, path: Expr) -> Partition {
    Partition {
        selected: expr::subtree(span, memory.clone(), path.clone()),
        remaining: expr::without(span, memory, path),
    }
}

/// Restore a detached child. The caller must have removed the displaced subtree
/// first; this also permits local loans to snapshot the remainder independently.
pub(in super::super) fn attach(span: &Span, remaining: Expr, path: Expr, child: Expr) -> Expr {
    expr::add(span, remaining, expr::prefix(span, child, path))
}

/// Replace one subtree while retaining every descriptor outside its path.
pub(in super::super) fn replace(span: &Span, memory: Expr, path: Expr, child: Expr) -> Expr {
    let partition = detach(span, memory, path.clone());
    attach(span, partition.remaining, path, child)
}

/// Logical effects of removing one sequence element. Capacity and backing bytes
/// are preserved by the caller. A pop from an empty sequence selects index -1,
/// whose subtree is empty for a valid runtime collection.
pub(in super::super) struct Removal {
    /// Selected index. Local accounting snapshots this before changing metadata.
    pub(in super::super) index: Expr,
    /// Occupied length after the operation, including an empty pop.
    pub(in super::super) length: Expr,
    /// Optional result tag: one for Some and zero for None. Remove has no tag.
    pub(in super::super) tag: Option<Expr>,
    /// Whether following siblings shift down to fill the removed index.
    reindex: bool,
}

impl Removal {
    pub(in super::super) fn pop(span: &Span, length: Expr) -> Self {
        let tag = growth::select(
            span,
            crate::ast_util::mk_ineq(span, &expr::integer(span, 0), &length, InequalityOp::Lt),
            expr::integer(span, 1),
            expr::integer(span, 0),
        );
        let index = contracts::subtract(span, length, expr::integer(span, 1));
        Self {
            length: contracts::maximum(span, expr::integer(span, 0), index.clone()),
            index,
            tag: Some(tag),
            reindex: false,
        }
    }

    /// The executable operation proves the index is within the occupied length.
    pub(in super::super) fn remove(span: &Span, length: Expr, index: Expr) -> Self {
        Self {
            index,
            length: contracts::maximum(
                span,
                expr::integer(span, 0),
                contracts::subtract(span, length, expr::integer(span, 1)),
            ),
            tag: None,
            reindex: true,
        }
    }

    pub(in super::super) fn path(&self, span: &Span) -> Expr {
        expr::push(span, expr::path(span, []), self.index.clone())
    }

    pub(in super::super) fn partition(&self, span: &Span, memory: Expr) -> Partition {
        let mut partition = detach(span, memory.clone(), self.path(span));
        if self.reindex {
            partition.remaining = expr::operation(
                span,
                "remove_index",
                vec![memory, self.index.clone()],
                expr::memory_type(),
            );
        }
        partition
    }
}
