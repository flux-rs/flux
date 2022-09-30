use std::fmt;

pub use rustc_ast::token::LitKind;
use rustc_hir::def_id::{DefId, LocalDefId};
pub use rustc_middle::ty::{FloatTy, IntTy, ParamTy, TyCtxt, UintTy};
pub use rustc_span::symbol::Ident;
use rustc_span::{Span, Symbol};

pub type AliasMap = rustc_hash::FxHashMap<Ident, Alias>;

#[derive(Debug)]
pub struct Qualifier {
    pub name: Ident,
    pub args: Vec<Param>,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct UFDef {
    /// name of the uninterpreted function
    pub name: Ident,
    /// input sorts
    pub inputs: Vec<Ident>,
    /// output sort
    pub output: Ident,
    /// definition source position
    pub span: Span,
}

#[derive(Debug)]
pub struct Alias<T = Ident> {
    pub name: Ident,
    pub args: Vec<Ident>,
    pub defn: Ty<T>,
    pub span: Span,
}

#[derive(Debug)]
pub struct StructDef<T = Ident> {
    pub def_id: LocalDefId,
    pub refined_by: Option<Params>,
    pub fields: Vec<Option<Ty<T>>>,
    pub opaque: bool,
}

#[derive(Debug)]
pub struct EnumDef<T = Ident> {
    pub def_id: LocalDefId,
    pub refined_by: Option<Params>,
    pub variants: Vec<VariantDef<T>>,
    pub opaque: bool,
}

#[derive(Debug)]
pub struct VariantDef<T = Ident> {
    pub fields: Vec<Ty<T>>,
    pub ret: Ty<T>,
    pub span: Span,
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
pub struct ConstSig {
    pub span: Span,
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
    /// example `x: nat` or `x: lb[0]`
    Alias(Ident, Path<T>, Indices),
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
    Indexed {
        path: Path<T>,
        indices: Indices,
    },
    /// ty{b:e}
    Exists {
        bind: Ident,
        path: Path<T>,
        pred: Expr,
    },
    /// Mutable or shared reference
    Ref(RefKind, Box<Ty<T>>),
    /// Strong reference, &strg<self: i32>
    StrgRef(Ident, Box<Ty<T>>),
    /// Constrained type: an exists without binder
    Constr(Expr, Box<Ty<T>>),
    /// ()
    Unit,
    Array(Box<Ty<T>>, Lit),
}

#[derive(Debug, Clone)]
pub struct Indices {
    pub indices: Vec<Index>,
    pub span: Span,
}

#[derive(Debug, Clone)]
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

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum Res {
    Bool,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Adt(DefId),
    Param(ParamTy),
}

#[derive(Eq, PartialEq, Clone, Copy, Debug)]
pub enum RefKind {
    Mut,
    Shr,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Var(Ident),
    Dot(Box<Expr>, Ident),
    Literal(Lit),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
    App(Ident, Vec<Expr>),
}

#[derive(Debug, Clone, Copy)]
pub struct Lit {
    pub kind: LitKind,
    pub symbol: Symbol,
    pub span: Span,
}

#[derive(Copy, Clone)]
pub enum BinOp {
    Iff,
    Imp,
    Or,
    And,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mod,
    Mul,
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
    pub fn assert_ty(self) -> Ty<R> {
        match self {
            Arg::Ty(ty) => ty,
            _ => panic!("not a type"),
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

impl fmt::Debug for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Iff => write!(f, "<=>"),
            BinOp::Imp => write!(f, "=>"),
            BinOp::Or => write!(f, "||"),
            BinOp::And => write!(f, "&&"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Ge => write!(f, ">="),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mod => write!(f, "mod"),
            BinOp::Mul => write!(f, "*"),
        }
    }
}

pub mod expand {
    use std::{collections::HashMap, iter};

    use rustc_span::{symbol::Ident, Span};

    use super::{AliasMap, Arg, BinOp, Expr, ExprKind, FnSig, Index, Indices, Path, Ty, TyKind};

    /// `expand_bare_sig(aliases, b_sig)` replaces all the alias-applications in `b_sig`
    /// with the corresponding type definitions from `aliases` (if any).
    pub fn expand_sig(aliases: &AliasMap, fn_sig: FnSig) -> Result<FnSig, Span> {
        Ok(FnSig {
            args: expand_args(aliases, fn_sig.args)?,
            returns: expand_ty(aliases, &fn_sig.returns),
            ensures: expand_locs(aliases, fn_sig.ensures),
            requires: fn_sig.requires,
            span: fn_sig.span,
        })
    }

    fn expand_args(aliases: &AliasMap, args: Vec<Arg>) -> Result<Vec<Arg>, Span> {
        args.into_iter()
            .map(|arg| expand_arg(aliases, arg))
            .collect()
    }

    fn expand_arg(aliases: &AliasMap, arg: Arg) -> Result<Arg, Span> {
        match arg {
            Arg::Alias(x, path, indices) => {
                match expand_alias(aliases, &path, &indices) {
                    Some(TyKind::Exists { bind: e_bind, path: e_path, pred: e_pred }) => {
                        Ok(expand_arg_exists(x, e_path, e_bind, e_pred))
                    }
                    _ => Err(path.span), // panic!("bad alias app: {:?}[{:?}]", &path, &indices),
                }
            }
            Arg::Indexed(x, path, None) => {
                match expand_alias0(aliases, &path) {
                    Some(TyKind::Exists { bind: e_bind, path: e_path, pred: e_pred }) => {
                        Ok(expand_arg_exists(x, e_path, e_bind, e_pred))
                    }
                    Some(_) => Err(path.span), // panic!("unexpected arg: expand_arg"),
                    None => Ok(Arg::Indexed(x, expand_path(aliases, &path), None)),
                }
            }
            Arg::Indexed(x, path, Some(e)) => {
                Ok(Arg::Indexed(x, expand_path(aliases, &path), Some(e)))
            }
            Arg::Ty(t) => Ok(Arg::Ty(expand_ty(aliases, &t))),
            Arg::StrgRef(x, t) => Ok(Arg::StrgRef(x, expand_ty(aliases, &t))),
        }
    }

    fn expand_arg_exists(x: Ident, e_path: Path, e_bind: Ident, e_pred: Expr) -> Arg {
        let subst = mk_sub1(e_bind, x);
        let x_pred = subst_expr(&subst, &e_pred);
        Arg::Indexed(x, e_path, Some(x_pred))
    }
    fn expand_alias0(aliases: &AliasMap, path: &Path) -> Option<TyKind> {
        let indices = Indices { indices: vec![], span: path.span };
        expand_alias(aliases, path, &indices)
    }

    fn expand_alias(aliases: &AliasMap, path: &Path, indices: &Indices) -> Option<TyKind> {
        let id = path.ident;
        match aliases.get(&id) {
            Some(alias) /* if path.args.is_empty() */ => {
                let subst = mk_sub(&alias.args, &indices.indices);
                let ty = subst_ty(&subst, &alias.defn);
                Some(ty.kind)
            }
            _ => None,
        }
    }

    fn expand_path(aliases: &AliasMap, path: &Path) -> Path {
        Path {
            ident: path.ident,
            args: path.args.iter().map(|t| expand_ty(aliases, t)).collect(),
            span: path.span,
        }
    }

    fn expand_ty(aliases: &AliasMap, ty: &Ty) -> Ty {
        let kind = expand_kind(aliases, &ty.kind);
        Ty { kind, span: ty.span }
    }

    fn expand_kind(aliases: &AliasMap, k: &TyKind) -> TyKind {
        match k {
            TyKind::Path(p) => {
                let indices = Indices { indices: vec![], span: p.span };
                match expand_alias(aliases, p, &indices) {
                    Some(k) => k,
                    None => TyKind::Path(expand_path(aliases, p)),
                }
            }
            TyKind::Exists { bind, path, pred } => {
                TyKind::Exists { bind: *bind, path: expand_path(aliases, path), pred: pred.clone() }
            }
            TyKind::Indexed { path, indices } => {
                match expand_alias(aliases, path, indices) {
                    Some(k) => k,
                    None => {
                        TyKind::Indexed {
                            path: expand_path(aliases, path),
                            indices: indices.clone(),
                        }
                    }
                }
            }
            TyKind::Ref(rk, t) => TyKind::Ref(*rk, Box::new(expand_ty(aliases, t))),
            TyKind::StrgRef(rk, t) => TyKind::StrgRef(*rk, Box::new(expand_ty(aliases, t))),
            TyKind::Unit => TyKind::Unit,
            TyKind::Constr(pred, t) => {
                TyKind::Constr(pred.clone(), Box::new(expand_ty(aliases, t)))
            }
            TyKind::Array(ty, len) => TyKind::Array(Box::new(expand_ty(aliases, ty)), *len),
        }
    }

    fn _and(e1: Expr, e2: Expr) -> Expr {
        let span = e1.span;
        let kind = ExprKind::BinaryOp(BinOp::And, Box::new(e1), Box::new(e2));
        Expr { kind, span }
    }

    fn expand_locs(aliases: &AliasMap, locs: Vec<(Ident, Ty)>) -> Vec<(Ident, Ty)> {
        locs.into_iter()
            .map(|(x, ty)| (x, expand_ty(aliases, &ty)))
            .collect()
    }

    type Subst = HashMap<Ident, Expr>;

    fn mk_sub1(src: Ident, dst: Ident) -> Subst {
        HashMap::from([(src, Expr { kind: ExprKind::Var(dst), span: dst.span })])
    }

    fn mk_sub(src: &Vec<Ident>, dst: &Vec<Index>) -> Subst {
        assert_eq!(src.len(), dst.len(), "mk_sub: invalid args");
        let mut res = HashMap::new();
        for (src_id, dst_ix) in iter::zip(src, dst) {
            match dst_ix {
                Index::Expr(e) => {
                    res.insert(*src_id, e.clone());
                }
                Index::Bind(_) => panic!("cannot use binder in type alias"),
                // TyKind::Path(p) if p.args.is_empty() => {
                //     res.insert(*src_id, p.ident);
                // }
                // _ => panic!("mk_sub: invalid arg"),
            }
        }
        res
    }

    fn subst_expr(subst: &Subst, e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::Var(x) => {
                match subst.get(x) {
                    Some(y) => y.clone(),
                    None => e.clone(),
                }
            }
            ExprKind::Literal(l) => Expr { kind: ExprKind::Literal(*l), span: e.span },
            ExprKind::BinaryOp(o, e1, e2) => {
                Expr {
                    kind: ExprKind::BinaryOp(
                        *o,
                        Box::new(subst_expr(subst, e1)),
                        Box::new(subst_expr(subst, e2)),
                    ),
                    span: e.span,
                }
            }
            ExprKind::Dot(e1, fld) => {
                Expr { kind: ExprKind::Dot(Box::new(subst_expr(subst, e1)), *fld), span: e.span }
            }
            ExprKind::App(f, es) => {
                let es = es.iter().map(|e| subst_expr(subst, e)).collect();
                Expr { kind: ExprKind::App(*f, es), span: e.span }
            }
        }
    }

    fn subst_path(subst: &Subst, p: &Path) -> Path {
        let mut args = vec![];
        for t in &p.args {
            args.push(subst_ty(subst, t));
        }
        Path { ident: p.ident, args, span: p.span }
    }

    fn subst_ty(subst: &Subst, ty: &Ty) -> Ty {
        Ty { kind: subst_tykind(subst, &ty.kind), span: ty.span }
    }

    fn subst_indices(subst: &Subst, i_indices: &Indices) -> Indices {
        let mut indices = vec![];
        for i in &i_indices.indices {
            indices.push(subst_index(subst, i));
        }
        Indices { indices, span: i_indices.span }
    }

    fn subst_index(subst: &Subst, i: &Index) -> Index {
        match i {
            super::Index::Expr(e) => Index::Expr(subst_expr(subst, e)),
            super::Index::Bind(_) => i.clone(),
        }
    }

    fn subst_tykind(subst: &Subst, k: &TyKind) -> TyKind {
        match k {
            TyKind::Path(p) => TyKind::Path(subst_path(subst, p)),
            TyKind::Indexed { path, indices } => {
                TyKind::Indexed {
                    path: subst_path(subst, path),
                    indices: subst_indices(subst, indices),
                }
            }
            TyKind::Exists { bind, path, pred } => {
                TyKind::Exists {
                    bind: *bind,
                    path: subst_path(subst, path),
                    pred: subst_expr(subst, pred),
                }
            }
            TyKind::Ref(rk, t) => TyKind::Ref(*rk, Box::new(subst_ty(subst, t))),
            TyKind::StrgRef(rk, t) => TyKind::StrgRef(*rk, Box::new(subst_ty(subst, t))),
            TyKind::Unit => TyKind::Unit,
            TyKind::Constr(pred, t) => {
                TyKind::Constr(subst_expr(subst, pred), Box::new(subst_ty(subst, t)))
            }
            TyKind::Array(ty, len) => TyKind::Array(Box::new(subst_ty(subst, ty)), *len),
        }
    }
}
