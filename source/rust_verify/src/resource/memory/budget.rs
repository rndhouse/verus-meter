//! Read erased resource clauses and checkpoints without evaluating their arguments.

use crate::context::BodyCtxt;
use crate::util::err_span;
use crate::verus_items::{SpecItem, VerusItem};
use rustc_ast::LitKind;
use rustc_hir::{BinOpKind, Expr, ExprKind};
use rustc_middle::ty::TyKind;
use vir::ast::VirErr;
use vir::def::Spanned;
use vir::resource::memory::{BudgetExpr, BudgetExprX};

pub(crate) fn lower<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr<'tcx>) -> Result<BudgetExpr, VirErr> {
    let node = match expr.kind {
        ExprKind::If(condition, then_expr, Some(else_expr)) => {
            let ghost = BodyCtxt { in_ghost: true, ..bctx.clone() };
            let condition =
                crate::rust_to_vir_expr::expr_to_vir(&ghost, condition)?.to_spec_expr(&ghost);
            BudgetExprX::If(condition, lower(bctx, then_expr)?, lower(bctx, else_expr)?)
        }
        ExprKind::Block(block, _) if block.stmts.is_empty() && block.expr.is_some() => {
            return lower(bctx, block.expr.unwrap());
        }
        ExprKind::Lit(lit) => match lit.node {
            LitKind::Int(n, _) => BudgetExprX::Literal(u64::try_from(n.get()).map_err(|_| {
                vir::messages::error(
                    &bctx.ctxt.spans.to_air_span(expr.span),
                    "resource budget must fit in u64",
                )
            })?),
            _ => return err_span(expr.span, "expected an integer resource budget"),
        },
        ExprKind::Binary(op, left, right) => {
            let left = lower(bctx, left)?;
            let right = lower(bctx, right)?;
            match op.node {
                BinOpKind::Add => BudgetExprX::Add(left, right),
                BinOpKind::Mul => BudgetExprX::Mul(left, right),
                _ => {
                    return err_span(
                        expr.span,
                        "resource budgets support only addition and multiplication",
                    );
                }
            }
        }
        ExprKind::Call(callee, args) => {
            let callee_type = bctx.types.expr_ty(callee);
            let TyKind::FnDef(id, substitutions) = callee_type.kind() else {
                return err_span(expr.span, "expected a size or mem_peak query in resource clause");
            };
            let substitutions = crate::rust_to_vir_base::fn_def_args(*substitutions, expr.span)?;
            let item = bctx.ctxt.get_verus_item(*id);
            let typ = match item {
                Some(VerusItem::Spec(SpecItem::ResourceSpecBudget)) if args.len() == 1 => {
                    let ghost = BodyCtxt { in_ghost: true, ..bctx.clone() };
                    let value = crate::rust_to_vir_expr::expr_to_vir(&ghost, &args[0])?
                        .to_spec_expr(&ghost);
                    return Ok(Spanned::new(
                        bctx.ctxt.spans.to_air_span(expr.span),
                        BudgetExprX::SpecCall(value),
                    ));
                }
                Some(VerusItem::Spec(SpecItem::ResourceQuantity)) if args.len() == 1 => {
                    let ExprKind::AddrOf(_, _, value) = args[0].kind else {
                        return err_span(expr.span, "expected a memory quantity name");
                    };
                    let ghost = BodyCtxt { in_ghost: true, ..bctx.clone() };
                    let value =
                        crate::rust_to_vir_expr::expr_to_vir(&ghost, value)?.to_spec_expr(&ghost);
                    return Ok(Spanned::new(
                        bctx.ctxt.spans.to_air_span(expr.span),
                        BudgetExprX::Quantity(value),
                    ));
                }
                Some(VerusItem::Spec(SpecItem::ResourceMemPeakCall)) if args.len() == 1 => {
                    let ExprKind::Call(function, arguments) = args[0].kind else {
                        return err_span(expr.span, "mem_peak expects a direct call");
                    };
                    let TyKind::FnDef(_, fn_args) = bctx.types.expr_ty(function).kind() else {
                        return err_span(function.span, "mem_peak expects a named function");
                    };
                    if !crate::rust_to_vir_base::fn_def_args(*fn_args, function.span)?.is_empty() {
                        return err_span(
                            function.span,
                            "generic function memory budgets are not supported",
                        );
                    }
                    let target = crate::rust_to_vir_expr::get_fn_path(bctx, function)?;
                    let ghost = BodyCtxt { in_ghost: true, ..bctx.clone() };
                    let arguments = arguments
                        .iter()
                        .map(|arg| {
                            Ok(crate::rust_to_vir_expr::expr_to_vir(&ghost, arg)?
                                .to_spec_expr(&ghost))
                        })
                        .collect::<Result<Vec<_>, VirErr>>()?;
                    return Ok(Spanned::new(
                        bctx.ctxt.spans.to_air_span(expr.span),
                        BudgetExprX::FunctionCall(target, std::sync::Arc::new(arguments)),
                    ));
                }
                Some(VerusItem::Spec(
                    SpecItem::ResourceOwnedSizeType | SpecItem::ResourceRefSizeType,
                )) if args.is_empty() => substitutions.type_at(0),
                Some(VerusItem::Spec(
                    SpecItem::ResourceOwnedSizeValue
                    | SpecItem::ResourceRefSizeValue
                    | SpecItem::ResourceMemPeak,
                )) if args.len() == 1 => {
                    let ExprKind::AddrOf(_, _, value) = args[0].kind else {
                        return err_span(expr.span, "expected a borrowed resource query argument");
                    };
                    if !matches!(value.kind, ExprKind::Path(_)) {
                        return err_span(
                            value.span,
                            "resource queries expect a local, parameter, or function name, not an evaluated expression",
                        );
                    }
                    let typ = substitutions.type_at(0);
                    if matches!(item, Some(VerusItem::Spec(SpecItem::ResourceMemPeak))) {
                        let TyKind::FnDef(_, fn_args) = typ.kind() else {
                            return err_span(
                                value.span,
                                "mem_peak expects a function with a declared resource contract",
                            );
                        };
                        if !crate::rust_to_vir_base::fn_def_args(*fn_args, value.span)?.is_empty() {
                            return err_span(
                                value.span,
                                "generic function memory budgets are not supported",
                            );
                        }
                        let fun = crate::rust_to_vir_expr::get_fn_path(bctx, value)?;
                        return Ok(Spanned::new(
                            bctx.ctxt.spans.to_air_span(expr.span),
                            BudgetExprX::Function(fun),
                        ));
                    }
                    typ
                }
                _ => {
                    return err_span(
                        expr.span,
                        "only owned_size, ref_size, and mem_peak queries are allowed in resource budgets",
                    );
                }
            };
            if matches!(
                item,
                Some(VerusItem::Spec(
                    SpecItem::ResourceRefSizeType | SpecItem::ResourceRefSizeValue
                ))
            ) {
                BudgetExprX::RefSize(bctx.mid_ty_to_vir(expr.span, &typ)?)
            } else {
                BudgetExprX::OwnedSize(bctx.mid_ty_to_vir(expr.span, &typ)?)
            }
        }
        _ => return err_span(expr.span, "unsupported resource budget expression"),
    };
    Ok(Spanned::new(bctx.ctxt.spans.to_air_span(expr.span), node))
}
