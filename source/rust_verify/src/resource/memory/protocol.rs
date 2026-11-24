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
    if !imported.is_empty() {
        definitions.extend(
            imports
                .iter()
                .flat_map(|krate| &krate.datatypes)
                .filter(|dt| imported.contains(&dt.x.name))
                .cloned(),
        );
    }
    definitions
}

/// Record which obligation would justify a bound for this concrete witness.
/// A method body can still fail verification. Discovery does not certify it.
pub(super) fn bind_holder_proofs(
    ctxt: &Context<'_>,
    krate: &mut KrateX,
    imports: &[Krate],
    evidence: &mut CompilerEvidence,
) {
    use vir::ast::{FunctionKind, Mode, TypX};
    let Some(id) = ctxt
        .tcx
        .get_diagnostic_item(Symbol::intern("verus::vstd::resource::holder::BoundedHolder"))
    else {
        return;
    };
    let Some(method) = ctxt
        .tcx
        .associated_items(id)
        .in_definition_order()
        .find(|item| ctxt.tcx.item_name(item.def_id).as_str() == "population_bound")
    else {
        return;
    };
    let declaration = ctxt.def_id_to_vir_path(method.def_id);
    let holder = |f: &vir::ast::Function| {
        let FunctionKind::TraitMethodImpl {
            method, trait_typ_args, inherit_body_from: None, ..
        } = &f.x.kind
        else {
            return None;
        };
        if method.path != declaration
            || f.x.mode != Mode::Proof
            || f.x.attrs.is_external_body
            || !f.x.typ_params.is_empty()
            || !f.x.typ_bounds.is_empty()
        {
            return None;
        }
        let [ty] = trait_typ_args.as_slice() else { return None };
        let TypX::Datatype(dt, args, _) = &**ty else { return None };
        args.is_empty().then(|| dt.clone())
    };
    for f in &mut krate.functions {
        if f.x.body.is_some()
            && let Some(dt) = holder(f)
        {
            evidence.holder_proofs.insert(dt, f.x.name.clone());
            // The exporter withholds this together with executable workspaces
            // until this proof and the crate's erased Rust checks have passed.
            Arc::make_mut(&mut Arc::make_mut(f).x.attrs).resource_body =
                Some(vir::resource::memory::synchronization::CheckedBody::erased_proof());
        }
    }
    for f in imports.iter().flat_map(|krate| &krate.functions) {
        if f.x.attrs.resource_body.is_some()
            && let Some(dt) = holder(f)
        {
            evidence.holder_proofs.insert(dt, f.x.name.clone());
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

/// Match an unconditional postcondition of the nominal vstd predicate on the
/// whole result and one executable shared input. No fact under an implication,
/// a user predicate or a projection of another return value qualifies.
pub(super) fn bind_issuers(krate: &KrateX, imports: &[Krate], evidence: &mut CompilerEvidence) {
    use vir::ast::*;
    fn name(expr: &Expr) -> Option<&VarIdent> {
        match &expr.x {
            ExprX::Var(name) => Some(name),
            ExprX::ReadPlace(place, _) if vir::ast_util::types_equal(&place.typ, &expr.typ) => {
                let PlaceX::Local(name) = &place.x else { return None };
                Some(name)
            }
            _ => None,
        }
    }
    let direct = vir::fun!(CrateId::Vstd => "resource", "holder"; "issued");
    let optional = vir::fun!(CrateId::Vstd => "resource", "holder"; "issued_on_success");
    let local = krate.functions.iter().filter(|f| f.x.body.is_some());
    let certified = imports
        .iter()
        .flat_map(|k| &k.functions)
        .filter(|f| evidence.imported_leaves.contains_key(&f.x.name));
    for f in local.chain(certified) {
        if f.x.mode != Mode::Exec
            || f.x.attrs.is_external_body
            || !matches!(f.x.kind, FunctionKind::Static)
        {
            continue;
        }
        for post in f.x.ensure.0.iter() {
            let ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, fun, _, _, _),
                args,
                post_args: None,
                body: None,
            } = &post.x
            else {
                continue;
            };
            if *fun != direct && *fun != optional {
                continue;
            }
            let [result, issuer] = args.as_slice() else { continue };
            if name(result) != Some(&f.x.inner_ret.x.name)
                || !vir::ast_util::types_equal(&result.typ, &f.x.inner_ret.x.typ)
            {
                continue;
            }
            if let Some(index) = f.x.params.iter().position(|p| {
                p.x.mode == Mode::Exec
                    && !p.x.user_mut
                    && matches!(&*p.x.typ, TypX::Decorate(TypDecoration::Ref, None, _))
                    && name(issuer) == Some(&p.x.name)
                    && vir::ast_util::types_equal(&issuer.typ, &p.x.typ)
            }) {
                let TypX::Decorate(_, _, receiver) = &*issuer.typ else { continue };
                let TypX::Datatype(dt, _, _) = &**receiver else { continue };
                evidence.issuer_types.insert(dt.clone());
                evidence.issuer_parameters.insert(f.x.name.clone(), index);
            }
        }
    }
}
