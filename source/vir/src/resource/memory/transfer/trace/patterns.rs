//! By-value pattern branches preserve the same parametric ownership as `if`.

use super::*;

impl Trace<'_> {
    pub(super) fn match_value(
        &mut self,
        span: &Span,
        source: &Place,
        arms: &Arms,
    ) -> Option<Value> {
        let value = self.place_value(source)?;
        self.branch_depth += 1;
        let before = self.state.clone();
        let mut branches = Vec::new();
        for arm in arms.iter() {
            if !matches!(&arm.x.guard.x, ExprX::Const(Constant::Bool(true))) {
                return None;
            }
            self.state = before.clone();
            let mut locals = Vec::new();
            let condition = self.pattern(&arm.x.pattern, value.clone(), &mut locals)?;
            let result = self.value(&arm.x.body)?;
            for name in locals {
                self.state.values.remove(&name);
                self.state.written.remove(&name);
            }
            branches.push((condition, self.state.clone(), result));
        }
        // Exhaustiveness is already checked by Rust. Earlier arms keep their
        // source order, including wildcard arms and nested optional patterns.
        let (_, mut state, mut result) = branches.pop()?;
        while let Some((condition, yes, value)) = branches.pop() {
            state = Self::join_state(span, condition.clone(), yes, state)?;
            result = Self::join_value(span, condition, &value, &result)?;
        }
        self.state = state;
        self.branch_depth -= 1;
        Some(result)
    }

    fn pattern(
        &mut self,
        pattern: &Pattern,
        value: Value,
        locals: &mut Vec<VarIdent>,
    ) -> Option<Expr> {
        let span = &pattern.span;
        match &pattern.x {
            PatternX::Wildcard => Some(crate::ast_util::mk_bool(span, true)),
            PatternX::Var(binding) if binding.by_ref == ByRef::No => {
                locals.push(binding.name.clone());
                self.state.values.insert(binding.name.clone(), value);
                Some(crate::ast_util::mk_bool(span, true))
            }
            PatternX::Constructor(_, variant, fields) if self.layouts.option(&pattern.typ) => {
                let Value::Owner(node) = value else { return None };
                let tag = property(span, node.memory.clone(), "length");
                match (variant.as_str(), fields.as_slice()) {
                    ("None", []) => Some(mk_eq(span, &tag, &expr::integer(span, 0))),
                    ("Some", [field]) => {
                        let payload = self.layouts.option_payload(&pattern.typ, span).ok()?.clone();
                        let minima = node
                            .minima
                            .into_iter()
                            .filter_map(|(path, floor)| {
                                path.strip_prefix(&[Step::Fixed(OwnerSlot::Contents)])
                                    .map(|path| (path.to_vec(), floor))
                            })
                            .collect();
                        let memory = expr::subtree(
                            span,
                            node.memory,
                            expr::path(span, [self.layouts.metadata_slot(&OwnerSlot::Contents)]),
                        );
                        let condition = self.pattern(
                            &field.a,
                            Value::Owner(Node { typ: payload, memory, minima }),
                            locals,
                        )?;
                        Some(crate::ast_util::conjoin(
                            span,
                            &vec![mk_eq(span, &tag, &expr::integer(span, 1)), condition],
                        ))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}
