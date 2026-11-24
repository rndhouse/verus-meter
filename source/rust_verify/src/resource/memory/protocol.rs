//! Resolve protocol proof dependencies and the reviewed vstd helpers whose
//! verified bodies supply importable workspace measurements.
use crate::context::Context;
use rustc_span::Symbol;
use std::collections::HashSet;
use std::sync::Arc;
use vir::ast::{Datatype, Dt, Fun, FunX, Krate, KrateX};
use vir::resource::memory::{BudgetExprX, ResourceContract, synchronization::CompilerEvidence};

const SEMAPHORE: &str = "verus::vstd::resource::semaphore::Semaphore";
const PERMIT: &str = "verus::vstd::resource::semaphore::Permit";

/// Size queries and the executable pass must see identical source fields, including
/// the private issuer reference and erased token of an imported permit. Only the
/// reviewed nominal vstd types extend the local layout universe.
pub(crate) fn layout_definitions(
    ctxt: &Context<'_>,
    local: &[Datatype],
    imports: &[Krate],
) -> Vec<Datatype> {
    let mut definitions = local.to_vec();
    let imported: HashSet<_> = [SEMAPHORE, PERMIT]
        .into_iter()
        .filter_map(|name| {
            let id = ctxt.tcx.get_diagnostic_item(Symbol::intern(name))?;
            (!id.is_local()).then(|| Dt::Path(ctxt.def_id_to_vir_path(id)))
        })
        .collect();
    definitions.extend(
        imports
            .iter()
            .flat_map(|krate| &krate.datatypes)
            .filter(|dt| {
                imported.contains(&dt.x.name)
                    || vir::resource::memory::synchronization::RwRecord::of(&dt.x.name).is_some()
            })
            .cloned(),
    );
    definitions
}

/// Record which obligation would justify a bound for this concrete witness.
/// A method body can still fail verification. Discovery does not certify it.
pub(super) fn bind_holder_proofs(
    krate: &mut KrateX,
    imports: &[Krate],
    evidence: &mut CompilerEvidence,
) {
    use vir::ast::*;
    let population =
        vir::fun!(CrateId::Vstd => "resource", "holder", "BoundedHolder"; "population_bound");
    let capacity = vir::fun!(CrateId::Vstd => "resource", "holder", "BoundedHolder"; "capacity");
    let incompatible =
        vir::fun!(CrateId::Vstd => "resource", "holder", "Incompatible"; "distinct_instances");
    let declarations: std::collections::HashMap<_, _> = krate
        .datatypes
        .iter()
        .chain(imports.iter().flat_map(|k| &k.datatypes))
        .map(|d| (d.x.name.clone(), d))
        .collect();
    // Erased lifetimes leave a concrete guard or a universally quantified
    // nominal record. A specialized implementation (or an extra bound on
    // its parameters) cannot supply a theorem at other instantiations.
    let universal = |f: &Function, ty: &Typ| {
        let TypX::Datatype(dt, args, _) = &**ty else { return None };
        let d = declarations.get(dt)?;
        (args.len() == f.x.typ_params.len() && d.x.typ_params.len() == args.len()
            && args.iter().zip(f.x.typ_params.iter().zip(d.x.typ_params.iter())).all(|(arg,(p,(formal,_)))|
                matches!(&**arg, TypX::TypParam(v) if v == p && v == formal))
            && f.x.typ_bounds.iter().all(|bound| d.x.typ_bounds.iter().any(|b|
                vir::ast_util::generic_bounds_equal(bound, b)))).then(|| dt.clone())
    };
    let mut register = |f: &Function| {
        let FunctionKind::TraitMethodImpl {
            method, trait_typ_args, inherit_body_from: None, ..
        } = &f.x.kind
        else {
            return false;
        };
        if f.x.mode != Mode::Proof || f.x.attrs.is_external_body {
            return false;
        }
        match trait_typ_args.as_slice() {
            [ty] if *method == population => {
                let Some(dt) = universal(f, ty) else { return false };
                evidence.holder_proofs.entry(dt).or_default().population = Some(f.x.name.clone());
            }
            [first, other] if *method == incompatible => {
                let (Some(left), Some(right)) = (universal(f, first), universal(f, other)) else {
                    return false;
                };
                evidence
                    .holder_proofs
                    .entry(left.clone())
                    .or_default()
                    .exclusions
                    .insert(right.clone(), (f.x.name.clone(), true));
                evidence
                    .holder_proofs
                    .entry(right)
                    .or_default()
                    .exclusions
                    .insert(left, (f.x.name.clone(), false));
            }
            _ => return false,
        }
        true
    };
    for f in &mut krate.functions {
        if f.x.body.is_some() && register(f) {
            Arc::make_mut(&mut Arc::make_mut(f).x.attrs).resource_body =
                Some(vir::resource::memory::synchronization::CheckedBody::erased_proof());
        }
    }
    for f in imports.iter().flat_map(|k| &k.functions) {
        if f.x.attrs.resource_body.is_some() {
            register(f);
        }
    }
    // A literal spec body establishes the same capacity even for acquisitions
    // whose postcondition supplies only the issuer identity.
    for f in krate.functions.iter().chain(imports.iter().flat_map(|k| &k.functions)) {
        if let FunctionKind::TraitMethodImpl {
            method, trait_typ_args, inherit_body_from: None, ..
        } = &f.x.kind
            && *method == capacity
            && !f.x.attrs.is_external_body
            && let [ty] = trait_typ_args.as_slice()
            && let Some(dt) = universal(f, ty)
            && evidence.holder_proofs.get(&dt).is_some_and(|role| role.population.is_some())
            && let Some(mut body) = f.x.body.as_ref()
        {
            while let ExprX::Block(stmts, Some(tail)) = &body.x {
                if !stmts.is_empty() {
                    break;
                }
                body = tail;
            }
            if let ExprX::Const(Constant::Int(value)) = &body.x
                && let Ok(limit) = u64::try_from(value.clone())
            {
                evidence.holder_proofs.entry(dt).or_default().constant_capacity = Some(limit);
            }
        }
    }
}

pub(super) fn bind_leaf_workspaces(
    ctxt: &Context<'_>,
    krate: &mut KrateX,
    imports: &[Krate],
    evidence: &mut CompilerEvidence,
) {
    let tcx = ctxt.tcx;
    let mut reviewed = HashSet::<Fun>::new();
    let mut record = |id| {
        reviewed.insert(Arc::new(FunX { path: ctxt.def_id_to_vir_path(id) }));
    };
    if let Some(id) = tcx
        .get_diagnostic_item(Symbol::intern("verus::vstd::invariant::spend_open_invariant_credit"))
    {
        record(id);
    }
    for (name, methods) in [
        ("verus::vstd::atomic::PAtomicUsize", &["fetch_add", "fetch_sub"][..]),
        ("verus::vstd::atomic_ghost::AtomicBool", &["new"][..]),
        ("verus::vstd::atomic_ghost::AtomicUsize", &["new"][..]),
        (PERMIT, &["release"][..]),
        (SEMAPHORE, &["new", "try_acquire", "acquire"][..]),
    ] {
        if let Some(id) = tcx.get_diagnostic_item(Symbol::intern(name)) {
            for imp in tcx.inherent_impls(id) {
                for item in tcx.associated_items(*imp).in_definition_order() {
                    if methods.contains(&tcx.item_name(item.def_id).as_str()) {
                        record(item.def_id);
                    }
                }
            }
        }
    }
    for function in imports.iter().flat_map(|krate| &krate.functions) {
        if function.x.mode == vir::ast::Mode::Exec
            && let Some(leaf) = function.x.attrs.resource_body
            && reviewed.contains(&function.x.name)
        {
            evidence.imported_leaves.insert(function.x.name.clone(), leaf);
        }
    }
    for function in &mut krate.functions {
        if reviewed.contains(&function.x.name) {
            evidence.measure_leaves.insert(function.x.name.clone());
            let budget =
                vir::def::Spanned::new(function.span.clone(), BudgetExprX::Literal(u64::MAX));
            Arc::make_mut(&mut Arc::make_mut(function).x.attrs).resource_contract =
                Some(ResourceContract { budget });
        }
    }
}

fn whole_name(expr: &vir::ast::Expr) -> Option<&vir::ast::VarIdent> {
    use vir::ast::*;
    match &expr.x {
        ExprX::Var(name) => Some(name),
        ExprX::ReadPlace(place, _) if vir::ast_util::types_equal(&place.typ, &expr.typ) => {
            let PlaceX::Local(name) = &place.x else { return None };
            Some(name)
        }
        _ => None,
    }
}

/// Match `result.holder_limit() == argument` on the whole constructor
/// result. A comparison inside an implication cannot supply an immutable limit.
fn capacity_parameter(
    function: &vir::ast::Function,
    post: &vir::ast::Expr,
    limit: &Fun,
) -> Option<usize> {
    use vir::ast::*;
    let ExprX::Binary(BinaryOp::Eq(Mode::Spec), lhs, rhs) = &post.x else { return None };
    let ExprX::Call {
        target: CallTarget::Fun(CallTargetKind::DynamicResolved { .. }, method, types, ..),
        args,
        post_args: None,
        body: None,
    } = &lhs.x
    else {
        return None;
    };
    let ([ty], [instance]) = (types.as_slice(), args.as_slice()) else { return None };
    let result = &function.x.inner_ret.x;
    let ExprX::ReadPlace(place, read) = &instance.x else { return None };
    if method != limit
        || !vir::ast_util::types_equal(ty, &result.typ)
        || !matches!(read.preliminary_kind, ReadKind::ImmutBor)
        || !matches!(&place.x, PlaceX::Local(n) if *n == result.name)
        || !vir::ast_util::types_equal(&place.typ, ty)
    {
        return None;
    }
    function.x.params.iter().position(|p| {
        p.x.mode == Mode::Exec
            && !p.x.user_mut
            && whole_name(rhs) == Some(&p.x.name)
            && matches!(&*p.x.typ, TypX::Int(IntRange::U(8 | 16 | 32 | 64) | IntRange::USize))
            && vir::ast_util::types_equal(&p.x.typ, &rhs.typ)
    })
}

/// Match an unconditional postcondition of the nominal vstd predicate on the
/// whole result and one executable shared input. No fact under an implication,
/// a user predicate or a projection of another return value qualifies.
pub(super) fn bind_issuers(krate: &KrateX, imports: &[Krate], evidence: &mut CompilerEvidence) {
    use vir::ast::*;
    let limit = vir::fun!(CrateId::Vstd => "resource", "holder", "BoundedInstance"; "holder_limit");
    let role = vir::fun!(CrateId::Vstd => "resource", "holder"; "role_of");
    let direct = vir::fun!(CrateId::Vstd => "resource", "holder"; "issued");
    let optional = vir::fun!(CrateId::Vstd => "resource", "holder"; "issued_on_success");
    let local = krate.functions.iter().filter(|f| f.x.body.is_some());
    let certified = imports.iter().flat_map(|k| &k.functions).filter(|f| {
        evidence.imported_leaves.contains_key(&f.x.name)
            || evidence.templates.contains_key(&f.x.name)
    });
    for f in local.chain(certified) {
        if f.x.mode != Mode::Exec
            || f.x.attrs.is_external_body
            || !matches!(f.x.kind, FunctionKind::Static)
        {
            continue;
        }
        for post in f.x.ensure.0.iter() {
            if let Some(index) = capacity_parameter(f, post, &limit) {
                evidence.capacity_parameters.insert(f.x.name.clone(), index);
            }
            let ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, fun, _, _, _),
                args,
                post_args: None,
                body: None,
            } = &post.x
            else {
                continue;
            };
            if *fun != direct && *fun != optional && *fun != role {
                continue;
            }
            let [result, issuer] = args.as_slice() else { continue };
            let whole = whole_name(result) == Some(&f.x.inner_ret.x.name)
                && vir::ast_util::types_equal(&result.typ, &f.x.inner_ret.x.typ);
            let writer = matches!(&result.x, ExprX::ReadPlace(p,_) if matches!(&p.x, PlaceX::Field(op, base)
                if op.datatype == Dt::Tuple(2) && op.field.as_str()=="1" && !op.get_variant &&
                matches!(op.check, VariantCheck::None) && matches!(&base.x, PlaceX::Local(n) if *n == f.x.inner_ret.x.name) &&
                vir::ast_util::types_equal(&base.typ, &f.x.inner_ret.x.typ) &&
                vir::resource::memory::synchronization::RwRecord::write_pair(&base.typ)
                    .is_some_and(|(_,handle)|vir::ast_util::types_equal(handle,&result.typ))));
            if !whole && !writer {
                continue;
            }
            if let Some(index) = f.x.params.iter().position(|p| {
                p.x.mode == Mode::Exec
                    && !p.x.user_mut
                    && matches!(&*p.x.typ, TypX::Decorate(TypDecoration::Ref, None, _))
                    && whole_name(issuer) == Some(&p.x.name)
                    && vir::ast_util::types_equal(&issuer.typ, &p.x.typ)
            }) {
                let TypX::Decorate(_, _, receiver) = &*issuer.typ else { continue };
                let TypX::Datatype(dt, _, _) = &**receiver else { continue };
                evidence.issuer_types.insert(dt.clone());
                if writer {
                    evidence.writer_issuers.insert(f.x.name.clone(), index);
                } else {
                    evidence.issuer_parameters.insert(f.x.name.clone(), (index, *fun != role));
                }
            }
        }
    }
}

/// Delay frame measurement until a concrete caller supplies its payload width.
/// The exporter withholds these original mode-checked bodies until verification
/// and erased Rust checks succeed, just as it withholds a measured workspace.
pub(super) fn bind_workspaces(
    ctxt: &Context<'_>,
    krate: &mut KrateX,
    imports: &[Krate],
    modes: &std::collections::HashMap<Fun, Arc<vir::resolution_inference::ResolutionInfo>>,
    evidence: &mut CompilerEvidence,
) {
    let tcx = ctxt.tcx;
    use vir::resource::memory::synchronization::WorkspaceMethod;
    let mut selected = std::collections::HashMap::new();
    for (ty, methods) in [
        (
            "verus::vstd::rwlock::RwLock",
            &["new", "acquire_read", "acquire_write", "into_inner"][..],
        ),
        ("verus::vstd::rwlock::ReadHandle", &["borrow", "release_read"][..]),
        ("verus::vstd::rwlock::WriteHandle", &["release_write"][..]),
        ("verus::vstd::cell::pcell_maybe_uninit::PCell", &["new", "take", "put", "borrow"][..]),
        ("verus::vstd::cell::pcell::PCell", &["replace"][..]),
    ] {
        let Some(id) = tcx.get_diagnostic_item(Symbol::intern(ty)) else { continue };
        for imp in tcx.inherent_impls(id) {
            for item in tcx.associated_items(*imp).in_definition_order() {
                let name = tcx.item_name(item.def_id);
                if methods.contains(&name.as_str()) {
                    let method = if ty.starts_with("verus::vstd::cell::") {
                        WorkspaceMethod::Cell
                    } else {
                        match name.as_str() {
                            "new" => WorkspaceMethod::New,
                            "acquire_read" => WorkspaceMethod::Read,
                            "acquire_write" => WorkspaceMethod::Write,
                            "borrow" => WorkspaceMethod::Borrow,
                            "release_read" => WorkspaceMethod::ReleaseRead,
                            "release_write" => WorkspaceMethod::ReleaseWrite,
                            "into_inner" => WorkspaceMethod::IntoInner,
                            _ => unreachable!(),
                        }
                    };
                    selected.insert(
                        Arc::new(FunX { path: ctxt.def_id_to_vir_path(item.def_id) }),
                        method,
                    );
                }
                if ty == "verus::vstd::cell::pcell::PCell"
                    && ["new", "borrow", "borrow_mut"].contains(&name.as_str())
                {
                    evidence
                        .workspace_primitives
                        .insert(Arc::new(FunX { path: ctxt.def_id_to_vir_path(item.def_id) }));
                }
            }
        }
    }
    if let Some(id) = tcx.lang_items().maybe_uninit() {
        for imp in tcx.inherent_impls(id) {
            for item in tcx.associated_items(*imp).in_definition_order() {
                if ["new", "uninit", "assume_init", "assume_init_ref"]
                    .contains(&tcx.item_name(item.def_id).as_str())
                {
                    evidence
                        .workspace_primitives
                        .insert(Arc::new(FunX { path: ctxt.def_id_to_vir_path(item.def_id) }));
                }
            }
        }
    }
    if let Some(id) = tcx.get_diagnostic_item(Symbol::intern("mem_swap")) {
        evidence.workspace_primitives.insert(Arc::new(FunX { path: ctxt.def_id_to_vir_path(id) }));
    }
    for f in &mut krate.functions {
        if let Some(&method) = selected.get(&f.x.name)
            && let Some(source) = modes.get(&f.x.name).and_then(|m| {
                vir::resource::memory::synchronization::WorkspaceSource::capture(method, f, m)
            })
        {
            Arc::make_mut(&mut Arc::make_mut(f).x.attrs).resource_template = Some(Arc::new(source));
            evidence.templates.insert(f.x.name.clone(), f.clone());
        }
    }
    for f in imports.iter().flat_map(|k| &k.functions) {
        if selected.contains_key(&f.x.name) && f.x.attrs.resource_template.is_some() {
            evidence.templates.insert(f.x.name.clone(), f.clone());
        }
    }
}
