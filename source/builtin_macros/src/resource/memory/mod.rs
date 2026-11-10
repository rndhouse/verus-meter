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
        ResourceExpr::Size(name, _, typ) => {
            let value_marker = Ident::new(&format!("resource_{name}_value"), name.span());
            let type_marker = Ident::new(&format!("resource_{name}_type"), name.span());
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
                    return quote_spanned_builtin!(builtin, expr.span() => #builtin::#value_marker(&#path));
                }
            }
            quote_spanned_builtin!(builtin, expr.span() => #builtin::#type_marker::<#typ>())
        }
        ResourceExpr::PeakCall(_, _, call) => {
            quote_spanned_builtin!(builtin, expr.span() => #builtin::resource_peak_call(#call))
        }
        ResourceExpr::Peak(_, _, function) => {
            quote_spanned_builtin!(builtin, expr.span() => #builtin::resource_peak(&#function))
        }
    }
}

impl Visitor {
    /// Resolve type queries in specifications without evaluating their operands.
    pub(in crate::syntax) fn handle_spec_size_query(&mut self, expr: &mut Expr) -> bool {
        if self.inside_ghost == 0 {
            return false;
        }
        let Expr::Call(call) = expr else {
            return false;
        };
        let Expr::Path(path) = &*call.func else {
            return false;
        };
        if !path.path.is_ident("owned_size") && !path.path.is_ident("ref_size") {
            return false;
        }
        let span = expr.span();
        let query = verus_syn::parse2::<verus_syn::ResourceExpr>(expr.to_token_stream());
        *expr = match query {
            Ok(query) => {
                let bindings = self.resource_bindings.clone();
                let value = lower_budget(self, &query, &bindings);
                Expr::Verbatim(quote_spanned_builtin!(builtin, span =>
                    #builtin::spec_cast_integer::<_, #builtin::nat>(#value)))
            }
            Err(error) => Expr::Verbatim(error.to_compile_error()),
        };
        true
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
            *expr = quote_verbatim!(span, attrs => ::core::compile_error!("memory sections require a verified exec function body"));
            return true;
        }
        // Resolve size-query names before visiting declarations in the section.
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
        if !matches!(expr, Expr::Assert(a) if matches!(a.expr, verus_syn::AssertExpr::Memory(..))) {
            return false;
        }
        let Expr::Assert(assert) = take_expr(expr) else { unreachable!() };
        let verus_syn::AssertExpr::Memory(query, _, resource) = assert.expr else { unreachable!() };
        let span = assert.assert_token.span;
        let attrs = assert.attrs;
        *expr = if self.inside_ghost > 0 || self.inside_external_code > 0 || self.inside_const {
            quote_verbatim!(span, attrs => ::core::compile_error!("memory checkpoints require a verified exec function body"))
        } else if self.erase_ghost.erase() {
            quote_verbatim!(span, attrs => ())
        } else {
            let bindings = self.resource_bindings.clone();
            let budget = lower_budget(self, &resource.budget, &bindings);
            if query == "current" {
                quote_verbatim!(builtin, span, attrs => #builtin::resource_assert_current_memory(#budget))
            } else {
                quote_verbatim!(builtin, span, attrs => #builtin::resource_assert_peak(#budget))
            }
        };
        true
    }
}
