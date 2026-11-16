//! Exercise recognition on resolved compiler definitions, including aliases and
//! identically spelled user methods. No OS synchronization is trusted by name.
use super::*;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Expr, ExprKind};
use rustc_interface::interface::Compiler;
use vir::resource::memory::synchronization::{LibraryType, Operation};

struct Probe {
    operations: Vec<Operation>,
    types: Vec<LibraryType>,
    guard_drop_recognized: bool,
}

impl Callbacks for Probe {
    fn after_analysis<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        struct Walk<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
            probe: &'a mut Probe,
        }
        impl<'tcx> Visitor<'tcx> for Walk<'_, 'tcx> {
            fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
                let def = match expr.kind {
                    ExprKind::MethodCall(..) => self.typeck.type_dependent_def_id(expr.hir_id),
                    ExprKind::Call(callee, _) => match &callee.kind {
                        ExprKind::Path(path) => {
                            self.typeck.qpath_res(path, callee.hir_id).opt_def_id()
                        }
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(def) = def {
                    if let Some(ResourceIntrinsic::Synchronization(operation)) = call(
                        self.tcx,
                        def,
                        None,
                        self.typeck.node_args(match expr.kind {
                            ExprKind::Call(callee, _) => callee.hir_id,
                            _ => expr.hir_id,
                        }),
                    ) {
                        self.probe.operations.push(operation);
                    }
                }
                if let TyKind::Adt(adt, _) = self.typeck.expr_ty(expr).kind()
                    && let Some(kind) = synchronization_type(self.tcx, adt.did())
                {
                    self.probe.types.push(kind);
                    if kind == LibraryType::MutexGuard {
                        let destructor =
                            adt.destructor(self.tcx).expect("standard guard destructor");
                        self.probe.guard_drop_recognized =
                            synchronization_call(self.tcx, destructor.did, self.tcx.mk_args(&[]))
                                == Some(Operation::GuardDrop);
                    }
                }
                intravisit::walk_expr(self, expr);
            }
        }
        for owner in tcx.hir_body_owners() {
            let body = tcx.hir_body_owned_by(owner);
            let typeck = tcx.typeck(owner);
            Walk { tcx, typeck, probe: self }.visit_body(body);
        }
        Compilation::Stop
    }
}

#[test]
fn compiler_recognizes_mutex_aliases_and_guard_traits_only() {
    // Run recognition inside the compiler with its existing virtual-file loader;
    // the fixture leaves no source or build artifact in the repository.
    struct Test {
        probe: Probe,
    }
    impl Callbacks for Test {
        fn config(&mut self, config: &mut rustc_interface::interface::Config) {
            config.file_loader = Some(Box::new(crate::trait_check::TCFileLoader {
                rust_code: r#"
use std::sync::{Mutex as RealMutex, MutexGuard};
use std::ops::{Deref, DerefMut};
type Alias = RealMutex<u64>;
struct Mutex;
impl Mutex {
    fn new() -> Self { Mutex }
    fn lock(&self) {}
    fn try_lock(&self) {}
}
pub fn real() {
    let lock = Alias::new(1);
    let mut guard = lock.lock().unwrap();
    let _ = <MutexGuard<'_, u64> as Deref>::deref(&guard);
    let _ = <MutexGuard<'_, u64> as DerefMut>::deref_mut(&mut guard);
    drop(guard);
    let _attempt = lock.try_lock();
}
pub fn unrelated() {
    let lock = Mutex::new(); lock.lock(); lock.try_lock();
}
fn lock<T>(_: T) {}
pub fn generic_lookalike(m: RealMutex<u64>) { lock(m); }
trait NamedLock { fn lock(&self) {} }
impl<T> NamedLock for RealMutex<T> {}
pub fn extension_lookalike(m: RealMutex<u64>) {
    <RealMutex<u64> as NamedLock>::lock(&m);
}
"#
                .into(),
            }));
        }
        fn after_analysis<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            self.probe.after_analysis(compiler, tcx)
        }
    }
    let mut test = Test {
        probe: Probe { operations: Vec::new(), types: Vec::new(), guard_drop_recognized: false },
    };
    rustc_driver::run_compiler(
        &[
            "rustc".into(),
            "--crate-name=sync_identity_test".into(),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "--sysroot".into(),
            String::from_utf8(
                std::process::Command::new("rustc")
                    .args(["--print", "sysroot"])
                    .output()
                    .expect("prepared rustc")
                    .stdout,
            )
            .unwrap()
            .trim()
            .into(),
            "dummyrs.rs".into(),
        ],
        &mut test,
    );
    assert_eq!(
        test.probe.operations,
        [
            Operation::MutexNew,
            Operation::MutexLock,
            Operation::GuardBorrow,
            Operation::GuardBorrowMut,
            Operation::MutexTryLock
        ]
    );
    assert!(test.probe.guard_drop_recognized);
    assert!(test.probe.types.contains(&LibraryType::Mutex));
    assert!(test.probe.types.contains(&LibraryType::MutexGuard));
    assert!(test.probe.types.contains(&LibraryType::Result));
}
