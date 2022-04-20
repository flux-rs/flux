pub use rustc_ast::token::LitKind;
use rustc_ast::Mutability;
use rustc_hir::def_id::DefId;
pub use rustc_middle::ty::{FloatTy, IntTy, ParamTy, UintTy};
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

use crate::ast;
pub use crate::ast::{Expr, ExprKind, Lit};

#[derive(Debug)]
pub enum BareSig {
    AstSig(ast::FnSig),
    SurSig(UnresFnSig),
}

#[derive(Debug)]
pub struct FnSig<P> {
    /// example: `l: i32@n`
    pub args: Vec<Arg<P>>,
    /// example `i32{v:v >= 0}`
    pub returns: Ty<P>,
    /// example: `*x: i32{v. v = n+1}`
    pub ensures: Vec<(Ident, Ty<P>)>,
    /// example: `where n > 0`
    pub requires: Option<Expr>,
    /// source span
    pub span: Span,
}

#[derive(Debug)]
pub enum Arg<P> {
    /// example `a: i32{a > 0}`
    Indexed(Ident, P, Option<Expr>),
    /// example `v: &strg i32`
    StrgRef(Ident, Ty<P>),
    /// example `i32`
    Ty(Ty<P>),
}

#[derive(Debug)]
pub struct Ty<T> {
    pub kind: TyKind<T>,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind<P> {
    /// ty
    Path(P),

    /// t[e]
    Indexed { path: P, indices: Indices },

    /// ty{b:e}
    Exists { bind: Ident, path: P, pred: Expr },

    /// Mutable or shared reference
    Ref(RefKind, Box<Ty<P>>),

    /// Strong reference, &strg<self: i32>
    StrgRef(Ident, Box<Ty<P>>),
}

#[derive(Debug)]
pub struct Indices {
    pub indices: Vec<Index>,
    pub span: Span,
}

#[derive(Debug)]
pub enum Index {
    /// @n
    Bind(Ident),
    Expr(Expr),
}

#[derive(Debug)]
pub struct UnresPath {
    /// e.g. vec
    pub ident: Ident,
    /// e.g. <nat>
    pub args: Option<Vec<Ty<Self>>>,
    pub span: Span,
}

#[derive(Debug)]
pub struct ResPath {
    pub kind: ResPathKind,
    pub args: Vec<Ty<Self>>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ResPathKind {
    Bool,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Adt(DefId),
    Param(ParamTy),
}

// -- Types moved over from `liquid-rust-core`

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Layout {
    Bool,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Adt(DefId),
    Ref,
    Param,
}

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum RefKind {
    Mut,
    Immut,
}

/// Bare (parsed) versions of surface signatures
pub type UnresTyKind = TyKind<UnresPath>;
pub type UnresTy = Ty<UnresPath>;
pub type UnresFnSig = FnSig<UnresPath>;
pub type UnresArg = Arg<UnresPath>;

/// Resolved versions of surface signatures (generated from rust-sigs)
pub type ResTyKind = TyKind<ResPath>;
pub type ResTy = Ty<ResPath>;
pub type ResFnSig = FnSig<ResPath>;
pub type ResArg = Arg<ResPath>;

impl ResPath {
    pub fn is_bool(&self) -> bool {
        matches!(self.kind, ResPathKind::Bool)
    }

    pub fn is_float(&self) -> bool {
        matches!(self.kind, ResPathKind::Float(_))
    }
}

impl<P> Arg<P> {
    #[track_caller]
    fn assert_ty(self) -> Ty<P> {
        match self {
            Arg::Ty(ty) => ty,
            Arg::Indexed(..) | Arg::StrgRef(..) => panic!("not a type"),
        }
    }
}

// ---------------------------------------------------------------------------
// -------------------------- DEFAULT Signatures -----------------------------
// ---------------------------------------------------------------------------

fn default_refkind(m: &Mutability) -> RefKind {
    match m {
        Mutability::Mut => RefKind::Mut,
        Mutability::Not => RefKind::Immut,
    }
}

fn default_path(ty: rustc_middle::ty::Ty) -> ResPath {
    let (kind, args) = match ty.kind() {
        rustc_middle::ty::TyKind::Bool => (ResPathKind::Bool, vec![]),
        rustc_middle::ty::TyKind::Int(int_ty) => (ResPathKind::Int(*int_ty), vec![]),
        rustc_middle::ty::TyKind::Uint(uint_ty) => (ResPathKind::Uint(*uint_ty), vec![]),
        rustc_middle::ty::TyKind::Float(float_ty) => (ResPathKind::Float(*float_ty), vec![]),
        rustc_middle::ty::TyKind::Param(param_ty) => (ResPathKind::Param(*param_ty), vec![]),
        rustc_middle::ty::TyKind::Adt(adt, substs) => {
            let substs = substs.types().map(default_ty).collect();
            (ResPathKind::Adt(adt.did), substs)
        }
        _ => todo!("`{ty:?}`"),
    };
    ResPath { kind, args, span: rustc_span::DUMMY_SP }
}

fn default_ty(ty: rustc_middle::ty::Ty) -> ResTy {
    let kind = match ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, ty, m) => {
            let ref_kind = default_refkind(m);
            let tgt_ty = default_ty(*ty);
            TyKind::Ref(ref_kind, Box::new(tgt_ty))
        }
        _ => TyKind::Path(default_path(ty)),
    };
    Ty { kind, span: rustc_span::DUMMY_SP }
}

pub fn default_fn_sig(rust_sig: rustc_middle::ty::FnSig) -> ResFnSig {
    let args = rust_sig
        .inputs()
        .iter()
        .map(|rust_ty| Arg::Ty(default_ty(*rust_ty)))
        .collect();
    let returns = default_ty(rust_sig.output());
    FnSig { args, returns, ensures: vec![], requires: None, span: rustc_span::DUMMY_SP }
}

pub mod zip {

    use std::{collections::HashMap, iter};

    use itertools::Itertools;
    use rustc_span::Symbol;

    use super::{
        FnSig, Ident, RefKind, ResArg, ResFnSig, ResPath, ResTy, Ty, TyKind, UnresArg, UnresFnSig,
        UnresPath, UnresTy,
    };

    type Locs = HashMap<Symbol, ResTy>;

    /// `zip_bare_def(b_sig, d_sig)` combines the refinements of the `b_sig` and the resolved elements
    /// of the (trivial/default) `dsig:DefFnSig` to compute a (refined) `DefFnSig`
    pub fn zip_bare_def(b_sig: UnresFnSig, d_sig: ResFnSig) -> ResFnSig {
        let mut locs: Locs = HashMap::new();
        let default_args = d_sig.args.into_iter().map(|arg| arg.assert_ty()).collect();
        FnSig {
            args: zip_args(b_sig.args, default_args, &mut locs),
            returns: zip_ty(b_sig.returns, &d_sig.returns),
            ensures: zip_ty_locs(b_sig.ensures, &locs),
            requires: b_sig.requires,
            span: b_sig.span,
        }
    }

    /// `zip_ty_locs` traverses the bare-outputs and zips with the location-types saved in `locs`
    fn zip_ty_locs(bindings: Vec<(Ident, UnresTy)>, locs: &Locs) -> Vec<(Ident, ResTy)> {
        let mut res = vec![];
        for (ident, ty) in bindings {
            if let Some(default) = locs.get(&ident.name) {
                let dt = zip_ty(ty, default);
                res.push((ident, dt))
            } else {
                panic!("missing location type for `{}`", ident)
            }
        }
        res
    }

    /// `zip_ty_binds` traverses the inputs `bs` and `ds` and
    /// saves the types of the references in `locs`
    fn zip_args(binds: Vec<UnresArg>, defaults: Vec<ResTy>, locs: &mut Locs) -> Vec<ResArg> {
        if binds.len() != defaults.len() {
            panic!(
                "bind count mismatch, expected: {:?},  found: {:?}",
                binds.len(),
                defaults.len()
            );
        }
        let binds = iter::zip(binds, &defaults)
            .map(|(arg, default)| zip_arg(arg, default))
            .collect_vec();
        for (arg, default) in iter::zip(&binds, defaults) {
            if let (ResArg::StrgRef(bind, _), TyKind::Ref(RefKind::Mut, default)) =
                (arg, default.kind)
            {
                locs.insert(bind.name, *default);
            }
        }
        binds
    }

    fn zip_arg(arg: UnresArg, default: &ResTy) -> ResArg {
        match (arg, &default.kind) {
            (UnresArg::Ty(ty), _) => ResArg::Ty(zip_ty(ty, default)),
            (UnresArg::Indexed(bind, path, pred), TyKind::Path(default)) => {
                ResArg::Indexed(bind, zip_path(path, default), pred)
            }
            (UnresArg::StrgRef(bind, ty), TyKind::Ref(RefKind::Mut, default)) => {
                ResArg::StrgRef(bind, zip_ty(ty, default))
            }
            _ => panic!("incompatible types `{default:?}`"),
        }
    }

    fn zip_ty(ty: UnresTy, default: &ResTy) -> ResTy {
        // we are assuming
        let kind = match (ty.kind, &default.kind) {
            (TyKind::Path(path), TyKind::Path(default)) => TyKind::Path(zip_path(path, default)),
            (TyKind::Indexed { path, indices }, TyKind::Path(default)) => {
                TyKind::Indexed { path: zip_path(path, default), indices }
            }
            (TyKind::Exists { bind, path, pred }, TyKind::Path(default)) => {
                TyKind::Exists { bind, path: zip_path(path, default), pred }
            }
            (TyKind::StrgRef(loc, ty), TyKind::Ref(RefKind::Mut, default)) => {
                TyKind::StrgRef(loc, Box::new(zip_ty(*ty, default)))
            }
            (TyKind::Ref(rk, ty), TyKind::Ref(default_rk, default)) if rk == *default_rk => {
                TyKind::Ref(rk, Box::new(zip_ty(*ty, default)))
            }
            _ => panic!("incompatible types `{default:?}`"),
        };
        Ty { kind, span: ty.span }
    }

    fn zip_path(path: UnresPath, default: &ResPath) -> ResPath {
        let args = path.args.unwrap_or_default();
        if args.len() != default.args.len() {
            panic!(
                "argument count mismatch, expected: {:?},  found: {:?}",
                default.args.len(),
                args.len()
            );
        }
        let args = iter::zip(args, &default.args)
            .map(|(ty, default)| zip_ty(ty, default))
            .collect();

        ResPath { kind: default.kind, args, span: path.span }
    }
}
