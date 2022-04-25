pub use rustc_ast::token::LitKind;
use rustc_ast::Mutability;
use rustc_hir::def_id::DefId;
pub use rustc_middle::ty::{FloatTy, IntTy, ParamTy, TyCtxt, UintTy};
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

pub use crate::ast::{Expr, ExprKind, Lit};

#[derive(Debug)]
pub struct AdtDef<T = Ident> {
    pub refined_by: Option<Params>,
    pub fields: Vec<Option<Ty<T>>>,
    pub opaque: bool,
}

#[derive(Debug)]
pub struct Params {
    pub params: Vec<Param>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Param {
    pub name: Ident,
    pub sort: Ident,
}

#[derive(Debug)]
pub struct FnSig<T = Ident> {
    /// example: `requires n > 0`
    pub requires: Option<Expr>,
    /// example: `i32<@n>`
    pub args: Vec<Arg<T>>,
    /// example `i32{v:v >= 0}`
    pub returns: Ty<T>,
    /// example: `*x: i32{v. v = n+1}`
    pub ensures: Vec<(Ident, Ty<T>)>,
    /// source span
    pub span: Span,
}

#[derive(Debug)]
pub enum Arg<T = Ident> {
    /// example `a: i32{a > 0}`
    Indexed(Ident, Path<T>, Option<Expr>),
    /// example `v: &strg i32`
    StrgRef(Ident, Ty<T>),
    /// example `i32`
    Ty(Ty<T>),
}

#[derive(Debug)]
pub struct Ty<R = Ident> {
    pub kind: TyKind<R>,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind<T = Ident> {
    /// ty
    Path(Path<T>),

    /// t[e]
    Indexed { path: Path<T>, indices: Indices },

    /// ty{b:e}
    Exists { bind: Ident, path: Path<T>, pred: Expr },

    /// Mutable or shared reference
    Ref(RefKind, Box<Ty<T>>),

    /// Strong reference, &strg<self: i32>
    StrgRef(Ident, Box<Ty<T>>),
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
pub struct Path<R = Ident> {
    /// e.g. vec
    pub ident: R,
    /// e.g. <nat>
    pub args: Vec<Ty<R>>,
    pub span: Span,
}

#[derive(Debug, Copy, Clone)]
pub enum Res {
    Bool,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Adt(DefId),
    Param(ParamTy),
}

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum RefKind {
    Mut,
    Shr,
}

impl Path<Res> {
    pub fn is_bool(&self) -> bool {
        matches!(self.ident, Res::Bool)
    }

    pub fn is_float(&self) -> bool {
        matches!(self.ident, Res::Float(_))
    }
}

impl<R> Arg<R> {
    #[track_caller]
    fn assert_ty(self) -> Ty<R> {
        match self {
            Arg::Ty(ty) => ty,
            Arg::Indexed(..) | Arg::StrgRef(..) => panic!("not a type"),
        }
    }
}

impl Params {
    pub fn empty(span: Span) -> Params {
        Params { params: vec![], span }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Param> {
        self.params.iter()
    }
}

impl IntoIterator for Params {
    type Item = Param;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.params.into_iter()
    }
}

// ---------------------------------------------------------------------------
// -------------------------- DEFAULT Signatures -----------------------------
// ---------------------------------------------------------------------------

fn default_refkind(m: &Mutability) -> RefKind {
    match m {
        Mutability::Mut => RefKind::Mut,
        Mutability::Not => RefKind::Shr,
    }
}

fn default_path(ty: rustc_middle::ty::Ty) -> Path<Res> {
    let (ident, args) = match ty.kind() {
        rustc_middle::ty::TyKind::Bool => (Res::Bool, vec![]),
        rustc_middle::ty::TyKind::Int(int_ty) => (Res::Int(*int_ty), vec![]),
        rustc_middle::ty::TyKind::Uint(uint_ty) => (Res::Uint(*uint_ty), vec![]),
        rustc_middle::ty::TyKind::Float(float_ty) => (Res::Float(*float_ty), vec![]),
        rustc_middle::ty::TyKind::Param(param_ty) => (Res::Param(*param_ty), vec![]),
        rustc_middle::ty::TyKind::Adt(adt, substs) => {
            let substs = substs.types().map(default_ty).collect();
            (Res::Adt(adt.did), substs)
        }
        _ => todo!("`{ty:?}`"),
    };
    Path { ident, args, span: rustc_span::DUMMY_SP }
}

fn default_ty(ty: rustc_middle::ty::Ty) -> Ty<Res> {
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

pub fn default_fn_sig(tcx: TyCtxt, def_id: DefId) -> FnSig<Res> {
    let rust_sig = tcx.erase_late_bound_regions(tcx.fn_sig(def_id));
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

    use super::{Arg, FnSig, Ident, Path, RefKind, Res, Ty, TyKind};

    type Locs = HashMap<Symbol, Ty<Res>>;

    /// `zip_bare_def(b_sig, d_sig)` combines the refinements of the `b_sig` and the resolved elements
    /// of the (trivial/default) `dsig:DefFnSig` to compute a (refined) `DefFnSig`
    pub fn zip_bare_def(b_sig: FnSig, d_sig: FnSig<Res>) -> FnSig<Res> {
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
    fn zip_ty_locs(bindings: Vec<(Ident, Ty)>, locs: &Locs) -> Vec<(Ident, Ty<Res>)> {
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
    fn zip_args(binds: Vec<Arg>, defaults: Vec<Ty<Res>>, locs: &mut Locs) -> Vec<Arg<Res>> {
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
            if let (Arg::StrgRef(bind, _), TyKind::Ref(RefKind::Mut, default)) = (arg, default.kind)
            {
                locs.insert(bind.name, *default);
            }
        }
        binds
    }

    fn zip_arg(arg: Arg, default: &Ty<Res>) -> Arg<Res> {
        match (arg, &default.kind) {
            (Arg::Ty(ty), _) => Arg::Ty(zip_ty(ty, default)),
            (Arg::Indexed(bind, path, pred), TyKind::Path(default)) => {
                Arg::Indexed(bind, zip_path(path, default), pred)
            }
            (Arg::StrgRef(bind, ty), TyKind::Ref(RefKind::Mut, default)) => {
                Arg::StrgRef(bind, zip_ty(ty, default))
            }
            _ => panic!("incompatible types `{default:?}`"),
        }
    }

    fn zip_ty(ty: Ty, default: &Ty<Res>) -> Ty<Res> {
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

    fn zip_path(path: Path, default: &Path<Res>) -> Path<Res> {
        if path.args.len() != default.args.len() {
            panic!(
                "argument count mismatch, expected: {:?},  found: {:?}",
                default.args.len(),
                path.args.len()
            );
        }
        let args = iter::zip(path.args, &default.args)
            .map(|(ty, default)| zip_ty(ty, default))
            .collect();

        Path { ident: default.ident, args, span: path.span }
    }
}
