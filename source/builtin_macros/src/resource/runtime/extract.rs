//! Retain immutable spec bindings as a shared expression graph. Inspect all
//! branches and initializers, including unused ones, before ghost erasure.
use proc_macro2::TokenStream;
use quote::{ToTokens, quote};
use std::collections::HashMap;
use verus_syn::ext::IdentExt;
use verus_syn::{
    BinOp, Block, Expr, ExprCall, FnArgKind, FnMode, ItemFn, Lit, Pat, ResourceExpr, ReturnType,
    Stmt, Type, UnOp,
};

type Environment = HashMap<String, Binding>;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Kind {
    Integer,
    Boolean,
}

impl Kind {
    pub fn constructor(self) -> TokenStream {
        match self {
            Self::Integer => quote!(::verus_meter_runtime::Expression),
            Self::Boolean => quote!(::verus_meter_runtime::BooleanExpression),
        }
    }
}

#[derive(Clone)]
pub(super) struct Binding {
    /// Compact reference to retained expression data (or an unretained input).
    pub tokens: TokenStream,
    /// Operand category, checked before composing typed nodes.
    pub kind: Kind,
    /// Declared type for size queries on a binding.
    pub ty: Option<Type>,
    /// Canonical node identity for sharing helper applications and local values.
    node: Option<usize>,
    /// Type tokens can contain span-sensitive macros, so those leaves stay distinct.
    intern: bool,
}

fn error(node: impl ToTokens, message: &str) -> verus_syn::Error {
    verus_syn::Error::new_spanned(node, message)
}

impl Binding {
    fn new(kind: Kind, tokens: TokenStream) -> Self {
        Self {
            kind,
            tokens,
            ty: (kind == Kind::Boolean).then(|| verus_syn::parse_quote!(bool)),
            node: None,
            intern: true,
        }
    }

    pub(super) fn parameter(kind: Kind, ty: Type, index: usize) -> Self {
        let constructor = kind.constructor();
        let mut binding = Self::new(kind, quote!(#constructor::parameter(#index)));
        binding.ty = Some(ty);
        binding
    }

    fn require(self, kind: Kind, node: impl ToTokens) -> verus_syn::Result<TokenStream> {
        if self.kind != kind {
            return Err(error(node, "incorrect expression type in runtime resource query"));
        }
        Ok(self.tokens)
    }
}

pub(super) struct Extractor<'a> {
    /// Functions declared alongside the annotated function before ghost erasure.
    functions: &'a HashMap<String, ItemFn>,
    /// Active helper and peak-target names, for dependency-cycle diagnostics.
    visiting: Vec<String>,
    /// Nodes are appended after their dependencies, so references point backward.
    nodes: Vec<TokenStream>,
    /// Intern structural expressions after child expressions have become references.
    interned: HashMap<(Kind, String), usize>,
    /// Reuse identical nonrecursive applications instead of expanding their bodies again.
    applications: HashMap<(String, Vec<usize>), Binding>,
    peaks: HashMap<(String, Vec<usize>), TokenStream>,
}

impl<'a> Extractor<'a> {
    pub fn new(functions: &'a HashMap<String, ItemFn>) -> Self {
        Self {
            functions,
            visiting: Vec::new(),
            nodes: Vec::new(),
            interned: HashMap::new(),
            applications: HashMap::new(),
            peaks: HashMap::new(),
        }
    }

    pub(super) fn nodes(&self) -> &[TokenStream] {
        &self.nodes
    }

    fn retain(&mut self, mut binding: Binding) -> Binding {
        if binding.node.is_some() {
            return binding;
        }
        let key = binding.intern.then(|| (binding.kind, binding.tokens.to_string()));
        let existing = key.as_ref().and_then(|key| self.interned.get(key)).copied();
        let index = if let Some(index) = existing {
            index
        } else {
            let index = self.nodes.len();
            let tokens = &binding.tokens;
            let node = match binding.kind {
                Kind::Integer => quote!(::verus_meter_runtime::BindingExpression::Integer(#tokens)),
                Kind::Boolean => quote!(::verus_meter_runtime::BindingExpression::Boolean(#tokens)),
            };
            self.nodes.push(node);
            if let Some(key) = key {
                self.interned.insert(key, index);
            }
            index
        };
        let constructor = binding.kind.constructor();
        binding.tokens = quote!(#constructor::binding(#index));
        binding.node = Some(index);
        binding
    }

    fn retain_size(&mut self, tokens: TokenStream) -> Binding {
        let mut binding = Binding::new(Kind::Integer, tokens);
        binding.intern = false;
        self.retain(binding)
    }

    pub fn budget(
        &mut self,
        budget: &ResourceExpr,
        env: &Environment,
    ) -> verus_syn::Result<TokenStream> {
        match budget {
            ResourceExpr::Size(name, _, ty) => {
                let size = self.size(name, ty, env)?;
                Ok(self.retain_size(size).tokens)
            }
            ResourceExpr::ReturnSize(_, _, function) => Ok(self.return_size(function)?.tokens),
            ResourceExpr::PeakCall(_, _, call) => self.peak_call(call, env),
            ResourceExpr::Peak(..) => Err(error(
                budget,
                "runtime peak(helper) queries are unsupported; use a shared numeric spec helper",
            )),
            ResourceExpr::SpecCall(call) => self.call(call, env)?.require(Kind::Integer, call),
            ResourceExpr::If(_, condition, _, left, _, _, right) => {
                let condition =
                    self.expression(condition, env)?.require(Kind::Boolean, condition)?;
                let left = self.budget(left, env)?;
                let right = self.budget(right, env)?;
                Ok(
                    quote!(::verus_meter_runtime::Expression::conditional(&#condition, &#left, &#right)),
                )
            }
            ResourceExpr::Paren(_, inner) => self.budget(inner, env),
            ResourceExpr::Add(left, _, right) | ResourceExpr::Mul(left, _, right) => {
                let left = self.budget(left, env)?;
                let right = self.budget(right, env)?;
                if matches!(budget, ResourceExpr::Add(..)) {
                    Ok(quote!(::verus_meter_runtime::Expression::add(&#left, &#right)))
                } else {
                    Ok(quote!(::verus_meter_runtime::Expression::multiply(&#left, &#right)))
                }
            }
            _ => self
                .expression(&verus_syn::parse2::<Expr>(budget.to_token_stream())?, env)?
                .require(Kind::Integer, budget),
        }
    }
    fn size(
        &self,
        name: &verus_syn::Ident,
        ty: &Type,
        env: &Environment,
    ) -> verus_syn::Result<TokenStream> {
        let ty = match ty {
            Type::Paren(paren) => return self.size(name, &paren.elem, env),
            Type::Path(path) if path.qself.is_none() => {
                match path.path.get_ident().and_then(|id| env.get(&id.unraw().to_string())) {
                    Some(binding) => binding.ty.as_ref().ok_or_else(|| {
                        error(ty, "runtime size query needs a declared source type")
                    })?,
                    None => ty,
                }
            }
            _ => ty,
        };
        Ok(super::super::memory::runtime::size(name, ty))
    }

    /// Use the source declaration for arity only. Rust resolves the function item
    /// and its actual output (including aliases and borrowed results) at the site.
    fn return_size(&mut self, target: &verus_syn::ExprPath) -> verus_syn::Result<Binding> {
        let same_scope = || {
            error(target, "runtime return_size requires a function in the same verus item scope")
        };
        if target.qself.is_some()
            || target.path.leading_colon.is_some()
            || target.path.segments.len() != 1
        {
            return Err(same_scope());
        }
        let name = target.path.segments[0].ident.unraw().to_string();
        let function = self.functions.get(&name).ok_or_else(same_scope)?;
        if !super::attributes::configuration(&function.attrs).is_empty()
            || !matches!(function.sig.mode, FnMode::Exec(_) | FnMode::Default)
            || function.sig.inputs.iter().any(|arg| arg.tracked.is_some())
            || matches!(function.sig.output, ReturnType::Type(_, Some(_), _, _))
            || function.sig.unsafety.is_some()
            || function.sig.abi.is_some()
        {
            return Err(error(
                target,
                "runtime return_size requires an unconditional safe Rust exec function with executable parameters and result",
            ));
        }
        let args: Vec<_> =
            (0..function.sig.inputs.len()).map(|index| quote::format_ident!("A{index}")).collect();
        let witness = quote!(::verus_meter_runtime::return_bytes({
            const fn output_type<#(#args,)* R>(_: fn(#(#args),*) -> R) -> ::core::marker::PhantomData<R> {
                ::core::marker::PhantomData
            }
            output_type
        }(#target)));
        Ok(self.retain_size(quote!(::verus_meter_runtime::Expression::constant(#witness))))
    }

    fn expression(&mut self, expr: &Expr, env: &Environment) -> verus_syn::Result<Binding> {
        let integer = quote!(::verus_meter_runtime::Expression);
        let boolean = quote!(::verus_meter_runtime::BooleanExpression);
        let binding = match expr {
            Expr::Lit(literal) => match &literal.lit {
                Lit::Bool(value) => Binding::new(Kind::Boolean, quote!(#boolean::constant(#value))),
                Lit::Int(value)
                    if matches!(value.suffix(), "" | "u8" | "u16" | "u32" | "u64" | "usize") =>
                {
                    let value = value.base10_parse::<u64>()?;
                    Binding::new(Kind::Integer, quote!(#integer::constant(#value)))
                }
                _ => return Err(error(expr, "unsupported literal in runtime resource query")),
            },
            Expr::Path(path) if path.qself.is_none() => {
                let name = path
                    .path
                    .get_ident()
                    .ok_or_else(|| error(path, "runtime queries require local scalar bindings"))?;
                env.get(&name.unraw().to_string()).cloned().ok_or_else(|| {
                    error(path, "unknown scalar binding in runtime resource query")
                })?
            }
            Expr::Paren(paren) => return self.expression(&paren.expr, env),
            Expr::Group(group) => return self.expression(&group.expr, env),
            Expr::Block(block) => return self.block(&block.block, env.clone()),
            Expr::Call(call) => return self.call(call, env),
            Expr::Cast(cast) => {
                if !matches!(&*cast.ty, Type::Path(path) if path.path.get_ident().is_some_and(|id| id == "nat" || id == "int"))
                {
                    return Err(error(
                        cast,
                        "runtime queries support only nonnegative mathematical nat/int casts; native casts are unsupported",
                    ));
                }
                // This fragment has no signed inputs, negative literals or subtraction.
                let mut binding = self.expression(&cast.expr, env)?;
                if binding.kind != Kind::Integer {
                    return Err(error(cast, "mathematical casts require an integer"));
                }
                binding.ty = Some((*cast.ty).clone());
                binding
            }
            Expr::Unary(unary) if matches!(unary.op, UnOp::Not(_)) => {
                let operand = self.expression(&unary.expr, env)?.require(Kind::Boolean, unary)?;
                Binding::new(Kind::Boolean, quote!(#boolean::not(&#operand)))
            }
            Expr::Binary(binary) => {
                let left = self.expression(&binary.left, env)?;
                let right = self.expression(&binary.right, env)?;
                let kind = left.kind;
                let a = left.tokens;
                let c = right.require(kind, binary)?;
                match &binary.op {
                    BinOp::Add(_) if kind == Kind::Integer => {
                        Binding::new(kind, quote!(#integer::add(&#a, &#c)))
                    }
                    BinOp::Mul(_) if kind == Kind::Integer => {
                        Binding::new(kind, quote!(#integer::multiply(&#a, &#c)))
                    }
                    BinOp::And(_) if kind == Kind::Boolean => {
                        Binding::new(kind, quote!(#boolean::and(&#a, &#c)))
                    }
                    BinOp::Or(_) if kind == Kind::Boolean => {
                        Binding::new(kind, quote!(#boolean::or(&#a, &#c)))
                    }
                    BinOp::Eq(_) | BinOp::Ne(_) if kind == Kind::Boolean => {
                        let equal = quote!(#boolean::or(&#boolean::and(&#a, &#c), &#boolean::and(&#boolean::not(&#a), &#boolean::not(&#c))));
                        Binding::new(
                            kind,
                            if matches!(binary.op, BinOp::Ne(_)) {
                                quote!(#boolean::not(&#equal))
                            } else {
                                equal
                            },
                        )
                    }
                    op if kind == Kind::Integer => {
                        let op = match op {
                            BinOp::Eq(_) => quote!(Equal),
                            BinOp::Ne(_) => quote!(NotEqual),
                            BinOp::Lt(_) => quote!(Less),
                            BinOp::Le(_) => quote!(LessEqual),
                            BinOp::Gt(_) => quote!(Greater),
                            BinOp::Ge(_) => quote!(GreaterEqual),
                            _ => {
                                return Err(error(
                                    binary,
                                    "unsupported arithmetic operation in runtime resource query",
                                ));
                            }
                        };
                        Binding::new(
                            Kind::Boolean,
                            quote!(#boolean::compare(::verus_meter_runtime::Comparison::#op, &#a, &#c)),
                        )
                    }
                    _ => {
                        return Err(error(
                            binary,
                            "unsupported Boolean operation in runtime resource query",
                        ));
                    }
                }
            }
            Expr::If(branch) => {
                let condition =
                    self.expression(&branch.cond, env)?.require(Kind::Boolean, branch)?;
                let left = self.block(&branch.then_branch, env.clone())?;
                let otherwise = branch
                    .else_branch
                    .as_ref()
                    .ok_or_else(|| error(branch, "runtime conditionals require else"))?;
                let right = self.expression(&otherwise.1, env)?;
                let a = left.require(Kind::Integer, branch)?;
                let c = right.require(Kind::Integer, branch)?;
                Binding::new(Kind::Integer, quote!(#integer::conditional(&#condition, &#a, &#c)))
            }
            _ => return Err(error(expr, "unsupported expression in runtime resource query")),
        };
        Ok(self.retain(binding))
    }
    fn block(&mut self, block: &Block, mut env: Environment) -> verus_syn::Result<Binding> {
        for (index, statement) in block.stmts.iter().enumerate() {
            match statement {
                Stmt::Local(local)
                    if local.tracked.is_none()
                        && local.ghost.is_none()
                        && local.attrs.is_empty() =>
                {
                    let (pattern, annotation) = match &local.pat {
                        Pat::Type(typed) => (&*typed.pat, Some((*typed.ty).clone())),
                        p => (p, None),
                    };
                    let Pat::Ident(name) = pattern else {
                        return Err(error(
                            local,
                            "runtime helper bindings require immutable scalar names",
                        ));
                    };
                    if name.mutability.is_some() || name.by_ref.is_some() || name.subpat.is_some() {
                        return Err(error(local, "runtime helper bindings must be immutable"));
                    }
                    let initializer =
                        local.init.as_ref().filter(|init| init.diverge.is_none()).ok_or_else(
                            || error(local, "runtime helper bindings require an initializer"),
                        )?;
                    let mut binding = self.expression(&initializer.expr, &env)?;
                    if let Some(ty) = annotation {
                        binding.ty = Some(ty);
                    }
                    env.insert(name.ident.unraw().to_string(), binding);
                }
                Stmt::Expr(expr, None) if index + 1 == block.stmts.len() => {
                    return self.expression(expr, &env);
                }
                _ => {
                    return Err(error(
                        statement,
                        "runtime spec helpers support immutable lets and a final scalar expression only",
                    ));
                }
            }
        }
        Err(error(block, "runtime spec helper requires a final expression"))
    }
    fn call(&mut self, call: &ExprCall, env: &Environment) -> verus_syn::Result<Binding> {
        let Expr::Path(path) = &*call.func else {
            return Err(error(
                call,
                "higher-order spec applications are unsupported in runtime queries",
            ));
        };
        let name = path.path.get_ident().ok_or_else(|| {
            error(call, "runtime spec helpers must be named in the same verus item scope")
        })?;
        if name == "return_size" {
            let ResourceExpr::ReturnSize(_, _, target) = verus_syn::parse2(call.to_token_stream())?
            else {
                return Err(error(call, "return_size expects a named function"));
            };
            return self.return_size(&target);
        }
        if ResourceExpr::is_size_query(name) {
            let ResourceExpr::Size(query, _, ty) = verus_syn::parse2(call.to_token_stream())?
            else {
                return Err(error(call, "invalid runtime model-size query"));
            };
            let size = self.size(&query, &ty, env)?;
            return Ok(self.retain_size(size));
        }
        let function = self.functions.get(&name.unraw().to_string()).cloned().ok_or_else(|| {
            error(call, "runtime spec helper is unavailable in this verus item scope")
        })?;
        if !super::attributes::configuration(&function.attrs).is_empty() {
            return Err(error(
                call,
                "runtime helper targets with cfg attributes are unsupported; use an unconditional helper with a conditional expression",
            ));
        }
        if !matches!(function.sig.mode, FnMode::Spec(_))
            || crate::syntax::has_external_code(&function.attrs)
            || function.semi_token.is_some()
            || !function.sig.generics.params.is_empty()
            || function.sig.generics.where_clause.is_some()
            || function.sig.inputs.len() != call.args.len()
        {
            return Err(error(
                call,
                "runtime queries require a local nongeneric spec helper with a checked body and matching scalar arguments",
            ));
        }
        if self.visiting.contains(&name.unraw().to_string()) {
            return Err(error(call, "recursive spec helpers are unsupported in runtime queries"));
        }
        let (bound, arguments) = self.arguments(&function, call, env)?;
        let key = (name.unraw().to_string(), arguments);
        if let Some(result) = self.applications.get(&key) {
            return Ok(result.clone());
        }
        self.visiting.push(name.unraw().to_string());
        let result = self.block(&function.block, bound);
        self.visiting.pop();
        let mut result = result?;
        if let ReturnType::Type(_, _, _, ty) = &function.sig.output {
            result.ty = Some((**ty).clone());
        }
        self.applications.insert(key, result.clone());
        Ok(result)
    }
    fn arguments(
        &mut self,
        function: &ItemFn,
        call: &ExprCall,
        env: &Environment,
    ) -> verus_syn::Result<(Environment, Vec<usize>)> {
        if function.sig.inputs.len() != call.args.len() {
            return Err(error(call, "incorrect runtime helper argument count"));
        }
        let mut bound = Environment::new();
        let mut arguments = Vec::new();
        for (parameter, argument) in function.sig.inputs.iter().zip(&call.args) {
            let FnArgKind::Typed(typed) = &parameter.kind else {
                return Err(error(parameter, "unsupported runtime helper parameter"));
            };
            let Pat::Ident(id) = &*typed.pat else {
                return Err(error(parameter, "unsupported runtime helper parameter"));
            };
            if parameter.tracked.is_some() || id.mutability.is_some() || id.by_ref.is_some() {
                return Err(error(
                    parameter,
                    "runtime helper parameters must be ordinary scalar names",
                ));
            }
            let mut value = self.expression(argument, env)?;
            value.ty = Some((*typed.ty).clone());
            let value = self.retain(value);
            arguments.push(value.node.expect("retained argument has a node identity"));
            bound.insert(id.ident.unraw().to_string(), value);
        }
        Ok((bound, arguments))
    }

    fn peak_call(&mut self, call: &ExprCall, env: &Environment) -> verus_syn::Result<TokenStream> {
        let Expr::Path(path) = &*call.func else {
            return Err(error(call, "runtime peak queries require a direct local function"));
        };
        let name = path.path.get_ident().ok_or_else(|| {
            error(call, "runtime peak queries require a function in the same verus item scope")
        })?;
        let function = self.functions.get(&name.unraw().to_string()).cloned().ok_or_else(|| {
            error(call, "runtime peak target unavailable in this verus item scope")
        })?;
        if !super::attributes::configuration(&function.attrs).is_empty() {
            return Err(error(
                call,
                "runtime peak targets with cfg attributes are unsupported; use an unconditional helper with a conditional expression",
            ));
        }
        if !matches!(function.sig.mode, FnMode::Exec(_) | FnMode::Default)
            || !function.sig.generics.params.is_empty()
            || crate::syntax::has_external_code(&function.attrs)
        {
            return Err(error(
                call,
                "runtime peak target must be a local nongeneric checked exec function",
            ));
        }
        let contract = function
            .sig
            .spec
            .resources
            .as_ref()
            .ok_or_else(|| error(call, "runtime peak target requires a resource contract"))?;
        if self.visiting.contains(&name.unraw().to_string()) {
            return Err(error(
                call,
                "recursive peak references are unsupported in runtime queries",
            ));
        }
        let (bound, arguments) = self.arguments(&function, call, env)?;
        let key = (name.unraw().to_string(), arguments);
        if let Some(result) = self.peaks.get(&key) {
            return Ok(result.clone());
        }
        self.visiting.push(name.unraw().to_string());
        let result = self.budget(&contract.budget, &bound);
        self.visiting.pop();
        let result = self.retain(Binding::new(Kind::Integer, result?)).tokens;
        self.peaks.insert(key, result.clone());
        Ok(result)
    }
}
