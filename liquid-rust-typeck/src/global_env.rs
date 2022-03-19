use std::cell::RefCell;

use liquid_rust_syntax::surface::Path;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
pub use rustc_middle::ty::Variance;
use rustc_middle::{mir::Mutability, ty::TyCtxt};
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

use crate::ty::{
    self,
    surface::{RefKind, TyKind},
    BaseTy, DefIdent, DefPath, DefTy, DefTyKind, Sort,
};

pub struct GlobalEnv<'tcx> {
    pub fn_specs: RefCell<FxHashMap<LocalDefId, ty::FnSpec>>,
    pub adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    pub tcx: TyCtxt<'tcx>,
}

fn default_refkind(m: &Mutability) -> RefKind {
    match m {
        Mutability::Mut => RefKind::Mut,
        Mutability::Not => RefKind::Immut,
    }
}

fn kind_def_ident(k: &rustc_middle::ty::TyKind) -> DefIdent {
    match k {
        rustc_middle::ty::TyKind::Bool => DefIdent::DBool,
        rustc_middle::ty::TyKind::Int(i) => DefIdent::DInt(*i),
        rustc_middle::ty::TyKind::Uint(u) => DefIdent::DUint(*u),
        rustc_middle::ty::TyKind::Adt(adt, _) => DefIdent::DAdt(adt.did),
        _ => panic!("kind_def_ident  : {:?}", k),
    }
}

fn default_base_path(k: &rustc_middle::ty::TyKind, span: Span) -> DefPath {
    Path { ident: kind_def_ident(k), args: None, span }
}

fn default_path(k: &rustc_middle::ty::TyKind, span: Span) -> DefPath {
    match k {
        rustc_middle::ty::TyKind::Bool => default_base_path(k, span),
        rustc_middle::ty::TyKind::Int(_) => default_base_path(k, span),
        rustc_middle::ty::TyKind::Uint(_) => default_base_path(k, span),
        rustc_middle::ty::TyKind::Adt(_, args) => {
            let ts = args.types().map(|arg| default_ty(&arg, span)).collect();
            Path { ident: kind_def_ident(k), args: Some(ts), span }
        }
        _ => panic!("default_path fails on: {:?}", k),
    }
}

fn default_ty_kind(k: &rustc_middle::ty::TyKind, span: Span) -> DefTyKind {
    match k {
        rustc_middle::ty::TyKind::Ref(_, ty, m) => {
            let ref_kind = default_refkind(m);
            let tgt_ty = default_ty(ty, span);
            TyKind::Ref(ref_kind, Box::new(tgt_ty))
        }
        _ => TyKind::Base(default_path(k, span)),
    }
}
fn default_ty(t: &rustc_middle::ty::Ty, span: Span) -> DefTy {
    let kind = default_ty_kind(t.kind(), span);
    ty::surface::Ty { kind, span }
}

fn mk_ident(i: i32, span: Span) -> Ident {
    let xstr = format!("def_x_{}", i);
    Ident::from_str_and_span(&xstr, span)
}

fn default_defn_sig(rust_sig: rustc_middle::ty::FnSig, span: Span) -> ty::DefFnSig {
    let mut requires = Vec::new();
    let mut i = 0;
    for t in rust_sig.inputs().iter() {
        let xi = mk_ident(i, span);
        let ti = default_ty(t, span);
        requires.push((xi, ti));
        i += 1
    }
    let returns = default_ty(&rust_sig.output(), span);
    let ensures = vec![];
    let wherep = None;
    ty::surface::FnSig { requires, returns, ensures, wherep, span }
}

fn desugar_defn_sig(_defn_sig: ty::DefFnSig) -> ty::FnSig {
    todo!() // <<<<<<< HEREHEREHERE
}

fn default_fn_spec(rust_sig: rustc_middle::ty::FnSig, span: Span) -> ty::FnSpec {
    let params = vec![];
    let defn_sig = default_defn_sig(rust_sig, span);
    let value = desugar_defn_sig(defn_sig);
    let fn_sig = ty::Binders { params, value };
    let assume = true;
    ty::FnSpec { fn_sig, assume }
}

impl<'tcx> GlobalEnv<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        fn_specs: RefCell<FxHashMap<LocalDefId, ty::FnSpec>>,
        adt_defs: FxHashMap<LocalDefId, ty::AdtDef>,
    ) -> Self {
        GlobalEnv { fn_specs, adt_defs, tcx }
    }

    pub fn lookup_fn_sig(&self, did: DefId, span: Span) -> ty::Binders<ty::FnSig> {
        // RJ:TODO -- make it cry when function is missing, THEN populate function from rust-sig.
        // Missing -- due to EXTERNAL crate OR because its LOCAL but had no annotations.
        // do this: https://ucsd-progsys.slack.com/archives/DU17X62Q5/p1647450667607229
        // see resolve Result<Resolver<'tcx>, ErrorReported> for error handling
        let local_def = did.as_local().unwrap();
        if let Some(fn_spec) = self.fn_specs.borrow().get(&local_def) {
            let z = fn_spec.fn_sig.clone();
            return z;
            // &self.fn_specs[&local_def].fn_sig
        }
        if let Some(rust_sig) = self.tcx.fn_sig(did).no_bound_vars() {
            let fn_spec = default_fn_spec(rust_sig, span);
            print!("Using default spec for function {:?} : {:?}", did, fn_spec);
            self.fn_specs
                .borrow_mut()
                .insert(local_def, fn_spec.clone());
            return fn_spec.fn_sig;
        }
        panic!("Oh no! lookup_fn_sig {:?}", did)
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn adt_def(&self, did: DefId) -> &ty::AdtDef {
        &self.adt_defs[&did.as_local().unwrap()]
    }

    pub fn sorts(&self, bty: &BaseTy) -> Vec<Sort> {
        match bty {
            BaseTy::Int(_) | BaseTy::Uint(_) => vec![Sort::int()],
            BaseTy::Bool => vec![Sort::bool()],
            BaseTy::Adt(def_id, _) => {
                if let Some(adt_def) = def_id.as_local().and_then(|did| self.adt_defs.get(&did)) {
                    adt_def.sorts()
                } else {
                    vec![]
                }
            }
        }
    }
}
