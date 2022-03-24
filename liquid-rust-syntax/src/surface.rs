pub use rustc_ast::token::LitKind;
use rustc_ast::Mutability;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;
pub use rustc_middle::ty::{FloatTy, IntTy, ParamTy, UintTy};
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

use crate::ast::{self, Expr, GenericParam, Refine};

#[derive(Debug)]
pub enum BareSig {
    AstSig(ast::FnSig),
    SurSig(BareFnSig),
}

#[derive(Debug)]
pub struct FnSig<T> {
    /// example: `l: i32@n`
    pub requires: Vec<(Ident, Ty<T>)>,
    /// example `i32{v:v >= 0}`
    pub returns: Ty<T>,
    /// example: `*x: i32{v:v = n+1}`
    pub ensures: Vec<(Ident, Ty<T>)>,
    /// example: `where n > 0`
    pub wherep: Option<Expr>,
    /// source span
    pub span: Span,
}

#[derive(Debug)]
pub struct Ty<T> {
    pub kind: TyKind<T>,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind<T> {
    /// ty
    Base(Path<T>),

    /// type parameters (not used in `Bare` but will show up after zipping)
    Param(ty::ParamTy),

    /// t[e]
    Refine { path: Path<T>, refine: Refine },

    /// ty{b:e}
    Exists { bind: Ident, path: Path<T>, pred: Expr },

    /// ty{e}, the param binder is used e.g. x: i32{0 < x}
    AnonEx { path: Path<T>, pred: Expr },

    /// named: n@t
    Named(Ident, Box<Ty<T>>),

    /// reference
    Ref(RefKind, Box<Ty<T>>),
}

#[derive(Debug)]
pub struct Path<T> {
    /// e.g. vec
    pub ident: T,
    /// e.g. <nat>
    pub args: Option<Vec<Ty<T>>>,
    pub span: Span,
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
    Weak,
    Mut,
    Immut,
}

struct Desugar {
    generics: Vec<ast::GenericParam>,
    args: Vec<ast::Ty>,
    reqs: Vec<(Ident, ast::Ty)>,
}

/// A `BindIn` is the information obtained from a single input-param binding
#[derive(Debug)]
struct BindIn {
    gen: Option<GenericParam>,
    ty: ast::Ty,
    loc: Option<(Ident, ast::Ty)>,
}

/// Bare (parsed) versions of surface signatures
pub type BarePath = Path<Ident>;
pub type BareTyKind = TyKind<Ident>;
pub type BareTy = Ty<Ident>;
pub type BareFnSig = FnSig<Ident>;

pub type DefIdent = Layout;

/// Resolved versions of surface signatures (generated from rust-sigs)
pub type DefPath = Path<DefIdent>;
pub type DefTyKind = TyKind<DefIdent>;
pub type DefTy = Ty<DefIdent>;
pub type DefFnSig = FnSig<DefIdent>;

fn convert_path(p: BarePath) -> ast::Path {
    ast::Path {
        ident: p.ident,
        span: p.span,
        args: p.args.map(|ts| ts.into_iter().map(convert_ty).collect()),
    }
}

fn convert_tykind(t: BareTyKind) -> ast::TyKind {
    match t {
        TyKind::Base(p) => ast::TyKind::BaseTy(convert_path(p)),
        TyKind::Exists { bind, path, pred } => {
            ast::TyKind::Exists { bind, path: convert_path(path), pred }
        }
        TyKind::AnonEx { .. } => {
            panic!("Unexpected input in convert_tykind!")
        }
        TyKind::Named(_, t) => {
            let ty = convert_ty(*t);
            ty.kind
        }
        TyKind::Ref(RefKind::Immut, t) => ast::TyKind::ShrRef(Box::new(convert_ty(*t))),
        TyKind::Ref(_, t) => ast::TyKind::WeakRef(Box::new(convert_ty(*t))),
        TyKind::Refine { path, refine } => {
            let path = convert_path(path);
            ast::TyKind::RefineTy { path, refine }
        }
        TyKind::Param(_) => panic!("impossible: Param in BareTyKind"),
    }
}

fn convert_ty(t: BareTy) -> ast::Ty {
    ast::Ty { kind: convert_tykind(t.kind), span: t.span }
}

fn is_bool(path: &BarePath) -> bool {
    path.ident.as_str() == "bool"
}

// HACK(ranjitjhala) need better way to determine if Path is a Type-Param
fn is_generic(path: &BarePath) -> bool {
    let str = path.ident.as_str();
    if let Some(c) = str.chars().next() {
        c.is_uppercase() && str.len() == 1
    } else {
        false
    }
}

fn is_float(path: &BarePath) -> bool {
    path.ident.as_str() == "f32" || path.ident.as_str() == "f64"
}

fn is_refinable(path: &BarePath) -> bool {
    !is_generic(path) && !is_float(path)
}

// HACK(ranjitjhala) need better way to "embed" rust types to sort
fn mk_sort(path: &BarePath, span: Span) -> Ident {
    let sort_name = if is_bool(path) { "bool" } else { "int" };
    Ident { name: rustc_span::Symbol::intern(sort_name), span }
}

fn mk_singleton(x: Ident) -> ast::Refine {
    let e = Expr { kind: ast::ExprKind::Var(x), span: x.span };
    ast::Refine { exprs: vec![e], span: x.span }
}

fn mk_generic(x: Ident, path: &BarePath, pred: Option<Expr>) -> ast::GenericParam {
    ast::GenericParam { name: x, sort: mk_sort(path, x.span), pred }
}

fn strengthen_pred(p: Option<Expr>, e: Expr) -> Expr {
    match p {
        None => e,
        Some(pe) => {
            let span = pe.span;
            let kind = ast::ExprKind::BinaryOp(ast::BinOp::And, Box::new(pe), Box::new(e));
            Expr { kind, span }
        }
    }
}

impl BindIn {
    fn from_path(x: Ident, single: bool, p: BarePath, span: Span, pred: Option<Expr>) -> BindIn {
        if single && is_refinable(&p) {
            let gen = Some(mk_generic(x, &p, pred));
            let path = convert_path(p);
            let refine = mk_singleton(x);
            let kind = ast::TyKind::RefineTy { path, refine };
            let ty = ast::Ty { kind, span };
            BindIn { gen, ty, loc: None }
        } else {
            let path = convert_path(p);
            let kind = ast::TyKind::BaseTy(path);
            let ty = ast::Ty { kind, span };
            BindIn { gen: None, ty, loc: None }
        }
    }

    fn from_ty(x: Ident, single: bool, ty: BareTy) -> BindIn {
        match ty.kind {
            TyKind::AnonEx { path, pred } => {
                BindIn::from_path(x, single, path, ty.span, Some(pred))
            }
            TyKind::Base(path) => BindIn::from_path(x, single, path, ty.span, None),
            TyKind::Refine { path, refine } => {
                let path = convert_path(path);
                let kind = ast::TyKind::RefineTy { path, refine };
                let ty = ast::Ty { kind, span: ty.span };
                BindIn { gen: None, ty, loc: None }
            }
            TyKind::Exists { bind, path, pred } => {
                let path = convert_path(path);
                let kind = ast::TyKind::Exists { bind, path, pred };
                let ty = ast::Ty { kind, span: ty.span };
                BindIn { gen: None, ty, loc: None }
            }
            TyKind::Named(n, t) => BindIn::from_ty(n, true, *t),
            TyKind::Ref(RefKind::Mut, t) => {
                let b = BindIn::from_ty(x, false, *t);
                let ty = ast::Ty { kind: ast::TyKind::StrgRef(x), span: ty.span };
                BindIn { gen: b.gen, ty, loc: Some((x, b.ty)) }
            }
            TyKind::Ref(RefKind::Immut, t) => {
                let b = BindIn::from_ty(x, false, *t);
                let ty = ast::Ty { kind: ast::TyKind::ShrRef(Box::new(b.ty)), span: ty.span };
                BindIn { gen: b.gen, ty, loc: None }
            }
            TyKind::Ref(RefKind::Weak, t) => {
                let b = BindIn::from_ty(x, false, *t);
                let ty = ast::Ty { kind: ast::TyKind::WeakRef(Box::new(b.ty)), span: ty.span };
                BindIn { gen: b.gen, ty, loc: None }
            }
            TyKind::Param(_) => panic!("IMPOSSIBLE: Param in BareTy"),
        }
    }
}

impl Desugar {
    fn desugar_inputs(&mut self, in_sigs: Vec<(Ident, BareTy)>) {
        for (x, ty) in in_sigs {
            let b_in = BindIn::from_ty(x, true, ty);
            if let Some(g) = b_in.gen {
                self.generics.push(g);
            }
            if let Some(l) = b_in.loc {
                self.reqs.push(l);
            }
            self.args.push(b_in.ty);
        }
    }

    pub fn desugar(ssig: BareFnSig) -> ast::FnSig {
        let mut me = Self { generics: vec![], args: vec![], reqs: vec![] };

        // walk over the input types
        me.desugar_inputs(ssig.requires);

        // Add the "where" clause to the last GenericParam
        if let Some(e) = ssig.wherep {
            if let Some(mut g) = me.generics.pop() {
                g.pred = Some(strengthen_pred(g.pred, e));
                me.generics.push(g);
            } else {
                panic!("'where' clause without generic params! {:?}", e.span);
            }
        }

        // translate the output store
        let ensures = ssig
            .ensures
            .into_iter()
            .map(|(x, ty)| (x, convert_ty(ty)))
            .collect();

        ast::FnSig {
            generics: ast::Generics { params: me.generics, span: ssig.span },
            args: me.args,
            requires: me.reqs,
            ret: convert_ty(ssig.returns),
            ensures,
            span: ssig.span,
        }
    }
}

pub fn desugar(ssig: BareFnSig) -> ast::FnSig {
    Desugar::desugar(ssig)
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

fn kind_def_ident(k: &rustc_middle::ty::TyKind) -> DefIdent {
    match k {
        rustc_middle::ty::TyKind::Bool => Layout::Bool,
        rustc_middle::ty::TyKind::Int(i) => Layout::Int(*i),
        rustc_middle::ty::TyKind::Uint(u) => Layout::Uint(*u),
        rustc_middle::ty::TyKind::Float(f) => Layout::Float(*f),
        rustc_middle::ty::TyKind::Adt(adt, _) => Layout::Adt(adt.did),
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
        rustc_middle::ty::TyKind::Float(_) => default_base_path(k, span),
        rustc_middle::ty::TyKind::Adt(_, args) => {
            let ts = args.types().map(|arg| default_ty(&arg, span)).collect();
            Path { ident: kind_def_ident(k), args: Some(ts), span }
        }

        _ => panic!("default_path fails on: {:?} at {:?}", k, span),
    }
}

fn default_ty_kind(k: &rustc_middle::ty::TyKind, span: Span) -> DefTyKind {
    match k {
        rustc_middle::ty::TyKind::Ref(_, ty, m) => {
            let ref_kind = default_refkind(m);
            let tgt_ty = default_ty(ty, span);
            TyKind::Ref(ref_kind, Box::new(tgt_ty))
        }
        rustc_middle::ty::TyKind::Param(a) => TyKind::Param(*a),
        _ => TyKind::Base(default_path(k, span)),
    }
}
fn default_ty(t: &rustc_middle::ty::Ty, span: Span) -> DefTy {
    let kind = default_ty_kind(t.kind(), span);
    Ty { kind, span }
}

fn mk_ident(i: i32, span: Span) -> Ident {
    let xstr = format!("def_x_{}", i);
    Ident::from_str_and_span(&xstr, span)
}

pub fn default_fn_sig(rust_sig: rustc_middle::ty::FnSig, span: Span) -> DefFnSig {
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
    FnSig { requires, returns, ensures, wherep, span }
}

mod erase {
    use super::{Path, Ty, TyKind};

    /// `erase::ty(t)` removes all refinements, so no `Refine` , `Exists`, `AnonEx` or `Named` constructors
    pub fn erase_ty<T: Copy>(ty: &Ty<T>) -> Ty<T> {
        Ty { kind: erase_ty_kind(&ty.kind), span: ty.span }
    }

    fn erase_ty_kind<T: Copy>(k: &TyKind<T>) -> TyKind<T> {
        match k {
            TyKind::Base(p) => TyKind::Base(erase_path(p)),
            TyKind::Param(a) => TyKind::Param(*a),
            TyKind::Refine { path, .. } => TyKind::Base(erase_path(path)),
            TyKind::Exists { path, .. } => TyKind::Base(erase_path(path)),
            TyKind::AnonEx { path, .. } => TyKind::Base(erase_path(path)),
            TyKind::Named(_, t) => erase_ty(t).kind,
            TyKind::Ref(r, t) => TyKind::Ref(*r, Box::new(erase_ty(t))),
        }
    }

    fn erase_path<T: Copy>(p: &Path<T>) -> Path<T> {
        let args = match &p.args {
            None => None,
            Some(ts) => Some(ts.into_iter().map(|t| erase_ty(&t)).collect()),
        };
        Path { ident: p.ident, args, span: p.span }
    }
}

pub mod zip {

    use std::collections::HashMap;

    use rustc_span::Span;

    use super::{
        erase::erase_ty, BareFnSig, BarePath, BareTy, BareTyKind, DefFnSig, DefPath, DefTy,
        DefTyKind, FnSig, Ident, Path, RefKind, Ty, TyKind,
    };

    type Locs = HashMap<Ident, DefTy>;

    /// `zip_bare_def(b_sig, d_sig)` combines the refinements of the `b_sig` and the resolved elements
    /// of the (trivial/default) `dsig:DefFnSig` to compute a (refined) `DefFnSig`
    pub fn zip_bare_def(b_sig: BareFnSig, d_sig: DefFnSig) -> DefFnSig {
        let mut locs: Locs = HashMap::new();
        FnSig {
            requires: zip_ty_binds(b_sig.requires, d_sig.requires, &mut locs),
            returns: zip_ty(b_sig.returns, d_sig.returns),
            ensures: zip_ty_locs(b_sig.ensures, &locs),
            wherep: b_sig.wherep,
            span: b_sig.span,
        }
    }

    /// `zip_ty_locs` traverses the bare-outputs and zips with the location-types saved in `locs`
    fn zip_ty_locs(bs: Vec<(Ident, BareTy)>, locs: &Locs) -> Vec<(Ident, DefTy)> {
        let mut res = vec![];
        for (x, bt) in bs.into_iter() {
            if let Some(dt) = locs.get(&x) {
                let dt = erase_ty(dt);
                let dt = zip_ty(bt, dt);
                res.push((x, dt))
            }
        }
        res
    }

    fn zip_ty(bty: BareTy, dty: DefTy) -> DefTy {
        let dty = erase_ty(&dty);
        Ty { kind: zip_ty_kind(bty.kind, dty.kind, bty.span), span: bty.span }
    }

    /// `zip_ty_binds` traverses the inputs `bs` and `ds` and
    /// saves the types of the references in `locs`
    fn zip_ty_binds(
        bs: Vec<(Ident, BareTy)>,
        ds: Vec<(Ident, DefTy)>,
        locs: &mut Locs,
    ) -> Vec<(Ident, DefTy)> {
        let mut res = vec![];
        for ((x, bt), (_, dt)) in itertools::zip_eq(bs, ds) {
            let dt_ = zip_ty_bind(x, bt, dt, locs);
            res.push((x, dt_));
        }
        return res;
    }

    fn zip_ty_bind(x: Ident, bt: BareTy, dt: DefTy, locs: &mut Locs) -> DefTy {
        if let TyKind::Ref(ref rk, ref dtt) = dt.kind {
            if *rk == super::RefKind::Mut {
                locs.insert(x, erase_ty(dtt));
            }
        }
        zip_ty(bt, dt)
    }

    fn zip_tys(bts: Vec<BareTy>, dts: Vec<DefTy>) -> Vec<DefTy> {
        let mut res = vec![];
        for (bt, dt) in itertools::zip_eq(bts, dts) {
            res.push(zip_ty(bt, dt))
        }
        return res;
    }

    fn zip_path(bp: BarePath, dp: DefPath) -> DefPath {
        let ident = dp.ident;
        let span = bp.span;
        let args = match (bp.args, dp.args) {
            (Some(bts), Some(dts)) => Some(zip_tys(bts, dts)),
            (None, None) => None,
            _ => panic!("zip_path: incompatible args!"),
        };
        Path { ident, args, span }
    }

    fn ref_compat(bk: RefKind, dk: RefKind) -> bool {
        match bk {
            RefKind::Mut => dk == RefKind::Mut,
            RefKind::Immut => dk == RefKind::Immut,
            RefKind::Weak => dk == RefKind::Mut,
        }
    }

    fn zip_ty_kind(bty: BareTyKind, dty: DefTyKind, span: Span) -> DefTyKind {
        match bty {
            TyKind::Base(bp) => {
                match dty {
                    TyKind::Base(dp) => TyKind::Base(zip_path(bp, dp)),
                    TyKind::Param(a) => TyKind::Param(a),
                    _ => panic!("zip_ty_kind: incompatible types"),
                }
            }
            TyKind::Refine { path, refine } => {
                match dty {
                    TyKind::Base(dp) => TyKind::Refine { path: zip_path(path, dp), refine },
                    TyKind::Param(_) => {
                        panic!("zip_ty_kind: cannot refine type variable! (singleton)")
                    }
                    _ => panic!("zip_ty_kind: incompatible types"),
                }
            }
            TyKind::Exists { bind, path, pred } => {
                match dty {
                    TyKind::Base(dp) => TyKind::Exists { bind, path: zip_path(path, dp), pred },
                    TyKind::Param(_) => panic!("zip_ty_kind: tyvar refined by existential!"),
                    _ => panic!("zip_ty_kind: incompatible types"),
                }
            }
            TyKind::AnonEx { path, pred } => {
                match dty {
                    TyKind::Base(dp) => TyKind::AnonEx { path: zip_path(path, dp), pred },
                    TyKind::Param(_) => panic!("zip_ty_kind: tyvar refined by (anon-existential)"),
                    _ => panic!("zip_ty_kind: incompatible types"),
                }
            }
            TyKind::Named(n, bt) => {
                let dt = zip_ty(*bt, Ty { kind: dty, span });
                TyKind::Named(n, Box::new(dt))
            }
            TyKind::Ref(bk, bt) => {
                match dty {
                    TyKind::Ref(dk, dt) => {
                        if ref_compat(bk, dk) {
                            TyKind::Ref(bk, Box::new(zip_ty(*bt, *dt)))
                        } else {
                            panic!("zip_ty: incompatible reference kinds at {:?}", span);
                        }
                    }
                    _ => panic!("zip_ty_kind: incompatible types"),
                }
            }
            TyKind::Param(_) => panic!("impossible: zip_ty_kind with param in bare"),
        }
    }
}
