//! Lower memory contracts while preserving executable code and ghost erasure.

use crate::syntax::{Visitor, take_expr};
use proc_macro2::TokenStream;
use quote::{ToTokens, quote, quote_spanned};
use verus_syn::spanned::Spanned;
use verus_syn::token::Semi;
use verus_syn::visit_mut::VisitMut;
use verus_syn::{Expr, ExprBlock, Ident, Stmt, Type};

/// Lower the small, parser-validated resource language without rewriting its
/// arithmetic into spec operators. Argument borrows exist only in erased headers.
pub(in crate::syntax) fn lower_budget(
    visitor: &mut Visitor,
    expr: &verus_syn::ResourceExpr,
    parameters: &[Ident],
) -> TokenStream {
    use verus_syn::ResourceExpr;
    match expr {
        ResourceExpr::If(_, condition, _, then_budget, _, _, else_budget) => {
            let then_budget = lower_budget(visitor, then_budget, parameters);
            let else_budget = lower_budget(visitor, else_budget, parameters);
            quote_spanned!(expr.span() => (if #condition { #then_budget } else { #else_budget }))
        }
        ResourceExpr::SpecCall(call) => {
            let mut call = Expr::Call(call.clone());
            let outer_ghost = visitor.inside_ghost;
            visitor.inside_ghost += 1;
            visitor.visit_expr_mut(&mut call);
            visitor.inside_ghost = outer_ghost;
            quote_spanned_builtin!(builtin, expr.span() => #builtin::resource_spec_budget(#call))
        }
        ResourceExpr::Literal(n) => n.to_token_stream(),
        ResourceExpr::Quantity(n) => {
            quote_spanned_builtin!(builtin, expr.span() => #builtin::resource_quantity(&#n))
        }
        ResourceExpr::Paren(_, e) => {
            let e = lower_budget(visitor, e, parameters);
            quote!((#e))
        }
        ResourceExpr::Add(left, op, right) => {
            let left = lower_budget(visitor, left, parameters);
            let right = lower_budget(visitor, right, parameters);
            quote_spanned!(expr.span() => (#left #op #right))
        }
        ResourceExpr::Mul(left, op, right) => {
            let left = lower_budget(visitor, left, parameters);
            let right = lower_budget(visitor, right, parameters);
            quote_spanned!(expr.span() => (#left #op #right))
        }
        ResourceExpr::MemSize(_, _, typ) => {
            // A simple name matching a parameter denotes its type. All other
            // arguments are Rust types, resolved by rustc (including aliases).
            let mut unwrapped = typ;
            while let Type::Paren(paren) = unwrapped {
                unwrapped = &paren.elem;
            }
            if let Type::Path(path) = unwrapped {
                if path.qself.is_none()
                    && path.path.get_ident().is_some_and(|id| parameters.contains(id))
                {
                    return quote_spanned_builtin!(builtin, expr.span() => #builtin::resource_mem_size_value(&#path));
                }
            }
            quote_spanned_builtin!(builtin, expr.span() => #builtin::resource_mem_size_type::<#typ>())
        }
        ResourceExpr::MemPeakCall(_, _, call) => {
            quote_spanned_builtin!(builtin, expr.span() => #builtin::resource_mem_peak_call(#call))
        }
        ResourceExpr::MemPeak(_, _, function) => {
            quote_spanned_builtin!(builtin, expr.span() => #builtin::resource_mem_peak(&#function))
        }
    }
}

impl Visitor {
    /// Minimum model reservation for a vector parameter, erased with contracts.
    pub(in crate::syntax) fn take_capacity_contracts(
        &mut self,
        attrs: &mut Vec<verus_syn::Attribute>,
        sig: &verus_syn::Signature,
    ) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        attrs.retain(|attr| {
            let path = attr.path();
            if path.segments.len() != 2 || path.segments[0].ident != "verifier"
                || path.segments[1].ident != "memory_capacity" { return true; }
            let span = attr.span();
            let parsed = attr.parse_args_with(|input: verus_syn::parse::ParseStream| {
                let parameter: Ident = input.parse()?;
                input.parse::<verus_syn::Token![,]>()?;
                let capacity: verus_syn::ResourceExpr = input.parse()?;
                Ok((parameter, capacity))
            });
            if !self.erase_ghost.erase() {
                let tokens = match parsed {
                    Ok((parameter, capacity)) if sig.spec.resources.is_some() => {
                        let capacity = lower_budget(self, &capacity, &[]);
                        quote_spanned_builtin!(builtin, span => #builtin::memory_capacity(&#parameter, #capacity))
                    }
                    Ok(_) => quote_spanned!(span => ::core::compile_error!("memory_capacity requires a mem_peak contract")),
                    Err(err) => err.to_compile_error(),
                };
                stmts.push(Stmt::Expr(Expr::Verbatim(tokens), Some(Semi { spans: [span] })));
            }
            false
        });
        stmts
    }

    /// Keep the executable block intact while attaching erased section metadata.
    pub(in crate::syntax) fn handle_resource_block(&mut self, expr: &mut Expr) -> bool {
        if !matches!(expr, Expr::ResourceBlock(_)) {
            return false;
        }
        let Expr::ResourceBlock(mut section) = take_expr(expr) else { unreachable!() };
        let span = section.contract.token.span;
        let attrs = section.attrs;
        if self.inside_ghost > 0 || self.inside_external_code > 0 || self.inside_const {
            *expr = quote_verbatim!(span, attrs => ::core::compile_error!("mem_peak sections require a verified exec function body"));
            return true;
        }
        // Resolve mem_size names before visiting declarations in the section.
        let bindings = self.resource_bindings.clone();
        let budget = lower_budget(self, &section.contract.budget, &bindings);
        self.visit_block_mut(&mut section.block);
        if !self.erase_ghost.erase() {
            section.block.stmts.insert(0, Stmt::Expr(
                Expr::Verbatim(quote_spanned_builtin!(builtin, span => #builtin::resource_section(#budget))),
                Some(Semi { spans: [span] }),
            ));
        }
        *expr = Expr::Block(ExprBlock { attrs, label: None, block: section.block });
        true
    }

    pub(in crate::syntax) fn handle_memory_checkpoint(&mut self, expr: &mut Expr) -> bool {
        if !matches!(expr, Expr::Assert(a) if matches!(a.expr, verus_syn::AssertExpr::MemPeak(..)))
        {
            return false;
        }
        let Expr::Assert(assert) = take_expr(expr) else { unreachable!() };
        let verus_syn::AssertExpr::MemPeak(_, _, resource) = assert.expr else { unreachable!() };
        let span = assert.assert_token.span;
        let attrs = assert.attrs;
        *expr = if self.inside_ghost > 0 || self.inside_external_code > 0 || self.inside_const {
            quote_verbatim!(span, attrs => ::core::compile_error!("mem_peak checkpoints require a verified exec function body"))
        } else if self.erase_ghost.erase() {
            quote_verbatim!(span, attrs => ())
        } else {
            let bindings = self.resource_bindings.clone();
            let budget = lower_budget(self, &resource.budget, &bindings);
            quote_verbatim!(builtin, span, attrs => #builtin::resource_assert_mem_peak(#budget))
        };
        true
    }
}
