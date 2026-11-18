//! Project producer storage into the suspended publisher's proof scope.
//! Conditional or unexportable body points retain their producer-local bindings.

use super::*;

impl Execution {
    /// Normal completion is an outgoing state of the producer, even if no
    /// caller has started waiting. The completion tag is charged by its owner.
    fn completed_storage(&self, span: &Span) -> Footprint {
        completed(span, self.retained.live_expression(span), self.result.value.bytes)
    }

    /// A worker with no possible interaction can finish while the publisher
    /// remains suspended inside spawn. An unknown call, destructor or wait
    /// keeps the overlap conditional on its effects for global composition.
    pub(super) fn pre_return_footprint(
        &self,
        span: &Span,
        descriptor: Option<&Expr>,
    ) -> Option<Footprint> {
        use crate::visitor::VisitorControlFlow::{Recurse, Return, Stop};
        // Use the source semantics of reviewed operations. An ordinary helper,
        // unknown destructor or synchronization call needs its own phase proof.
        let mut straight_line = true;
        let independent = crate::ast_visitor::expr_visitor_dfs(
            &self.effects.body,
            &mut air::scope_map::ScopeMap::new(),
            &mut |_, e| {
                if crate::resource::memory::execution::ignored_expression(e)
                    || matches!(e.x, ExprX::NonSpecClosure { .. })
                {
                    return Return;
                }
                if matches!(
                    e.x,
                    ExprX::If(..)
                        | ExprX::Match(..)
                        | ExprX::Loop { .. }
                        | ExprX::Return(..)
                        | ExprX::Logical(..)
                ) {
                    straight_line = false;
                }
                if let ExprX::Call { target, .. } = &e.x {
                    use ResourceIntrinsic::*;
                    if !matches!(target, CallTarget::Fun(_, _, _, _, attrs) if matches!(
                        attrs.resource_intrinsic, Some(ArrayRepeat | SliceLen | ArrayUnsize | BoxNew
                        | VecNew | VecWithCapacity | VecPush | VecPop | VecRemove | VecLen
                        | VecAsSlice | VecAsMutSlice | VecIntoBoxedSlice | OptionIsSome | OptionIsNone)
                    )) {
                        return Stop(());
                    }
                }
                Recurse
            },
        );
        if matches!(independent, Stop(())) {
            return None;
        }
        let retained = self.exported_completion(span, descriptor);
        if straight_line {
            // The publisher may stay suspended through these source points.
            // Only closed costs can cross into its scope without substitution.
            // Branch-local costs remain in the worker with their path conditions.
            // Fold constant totals first. A symbolic max duplicates its left
            // operand in both the condition and one arm of the generated VIR.
            let fixed = self
                .report
                .cost_points
                .iter()
                .map(|(_, cost)| cost)
                .filter(|cost| contracts::constant(&cost.total()).is_some())
                .cloned()
                .reduce(|a, b| a.maximum(span, b));
            if let Some(fixed) = fixed {
                return Some(retained.maximum(span, fixed));
            }
        }
        Some(retained)
    }

    fn exported_completion(&self, span: &Span, descriptor: Option<&Expr>) -> Footprint {
        let retained = self.completed_storage(span);
        if contracts::constant(&retained.total()).is_some() {
            return retained;
        }
        // A worker-local proof variable cannot escape. Use the result forest
        // specialized at this publication for owned descendants. Imported
        // allocations stay with their charging frame; shared links cost zero.
        let mut bytes = contracts::literal(span, self.result.value.bytes);
        if let Some(forest) = descriptor
            && self
                .entry
                .storage
                .owner
                .as_ref()
                .is_none_or(|o| o.complete() && o.inputs().is_empty())
        {
            use crate::resource::memory::{metadata::expr, transfer::simplify};
            let owned =
                simplify::simplify(&expr::cost(span, forest.clone(), expr::integer(span, 0)));
            bytes = contracts::add(span, bytes, owned);
        }
        Footprint::charge(MemoryKind::host_heap(), bytes)
    }
}
