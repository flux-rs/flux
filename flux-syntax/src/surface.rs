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
    pub args: Vec<RefineParam>,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct Defn {
    pub name: Ident,
    pub args: RefinedBy,
    pub sort: Sort,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct UifDef {
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
    pub refined_by: Option<RefinedBy>,
    pub fields: Vec<Option<Ty<T>>>,
    pub opaque: bool,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct EnumDef<T = Ident> {
    pub def_id: LocalDefId,
    pub refined_by: Option<RefinedBy>,
    pub variants: Vec<VariantDef<T>>,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct VariantDef<T = Ident> {
    pub fields: Vec<Ty<T>>,
    pub ret: VariantRet<T>,
    pub span: Span,
}

#[derive(Debug)]
pub struct VariantRet<T = Ident> {
    pub path: Path<T>,
    /// Binders are not allowed at this position, but we parse this as a list of indices
    /// for better error reporting.
    pub indices: Indices,
}

#[derive(Debug, Default)]
pub struct RefinedBy {
    pub params: Vec<RefineParam>,
    pub span: Span,
}

#[derive(Debug)]
pub struct RefineParam {
    pub name: Ident,
    pub sort: Sort,
}

#[derive(Debug)]
pub enum Sort {
    /// A _base_ sort, e.g., `int` or `bool`.
    Base(Ident),
    /// A _function_ sort of the form `(bi,...) -> bo` where `bi..` and `bo`
    /// are all base sorts.
    Func {
        inputs: Vec<Ident>,
        output: Ident,
    },
    Infer,
}

#[derive(Debug)]
pub struct ConstSig {
    pub span: Span,
}

#[derive(Debug)]
pub struct FnSig<T = Ident> {
    /// List of explicit refinement parameters
    pub params: Vec<RefineParam>,
    /// example: `requires n > 0`
    pub requires: Option<Expr>,
    /// example: `i32<@n>`
    pub args: Vec<Arg<T>>,
    /// example `i32{v:v >= 0}`
    pub returns: Option<Ty<T>>,
    /// example: `*x: i32{v. v = n+1}`
    pub ensures: Vec<(Ident, Ty<T>)>,
    /// source span
    pub span: Span,
}

#[derive(Debug)]
pub enum Arg<T = Ident> {
    /// example `a: i32{a > 0}`
    Constr(Ident, Path<T>, Expr),
    /// example `x: nat` or `x: lb[0]`
    Alias(Ident, Path<T>, Indices),
    /// example `v: &strg i32`
    StrgRef(Ident, Ty<T>),
    /// A type with an optional binder, e.g, `i32`, `x: i32` or `x: i32{v : v > 0}`.
    /// The binder has a different meaning depending on the type.
    Ty(Option<Ident>, Ty<T>),
}

#[derive(Debug)]
pub struct Ty<R = Ident> {
    pub kind: TyKind<R>,
    pub span: Span,
}

#[derive(Debug)]
pub enum BaseTy<T = Ident> {
    Path(Path<T>),
    Array(Box<Ty<T>>, ArrayLen),
    Slice(Box<Ty<T>>),
}

#[derive(Debug)]
pub enum TyKind<T = Ident> {
    /// ty
    Base(BaseTy<T>),
    /// `t[e]`
    Indexed {
        base: BaseTy<T>,
        indices: Indices,
    },
    /// ty{b:e}
    Exists {
        bind: Ident,
        base: BaseTy<T>,
        pred: Expr,
    },
    /// Mutable or shared reference
    Ref(RefKind, Box<Ty<T>>),
    /// Constrained type: an exists without binder
    Constr(Expr, Box<Ty<T>>),
    Tuple(Vec<Ty<T>>),
}

#[derive(Debug, Clone, Copy)]
pub struct ArrayLen;

#[derive(Debug, Clone)]
pub struct Indices {
    pub indices: Vec<RefineArg>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum RefineArg {
    /// `@n`, the span correspond to the span of `@` plus the identifier
    Bind(Ident, Span),
    Expr(Expr),
    Abs(Vec<Ident>, Expr, Span),
}

#[derive(Debug)]
pub struct Path<R = Ident> {
    pub ident: R,
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
    Str,
    Char,
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
    BinaryOp(BinOp, Box<[Expr; 2]>),
    App(Ident, Vec<Expr>),
    IfThenElse(Box<[Expr; 3]>),
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
    Ne,
    Add,
    Sub,
    Mod,
    Mul,
}

impl RefinedBy {
    pub const DUMMY: &RefinedBy = &RefinedBy { params: vec![], span: rustc_span::DUMMY_SP };
}

impl Path<Res> {
    pub fn is_bool(&self) -> bool {
        matches!(self.ident, Res::Bool)
    }

    pub fn is_float(&self) -> bool {
        matches!(self.ident, Res::Float(_))
    }
}

impl RefinedBy {
    pub fn iter(&self) -> impl Iterator<Item = &RefineParam> {
        self.params.iter()
    }
}

impl<'a> IntoIterator for &'a RefinedBy {
    type Item = &'a RefineParam;

    type IntoIter = std::slice::Iter<'a, RefineParam>;

    fn into_iter(self) -> Self::IntoIter {
        self.params.iter()
    }
}

impl IntoIterator for RefinedBy {
    type Item = RefineParam;

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
            BinOp::Ne => write!(f, "!="),
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

    use rustc_errors::ErrorGuaranteed;
    use rustc_span::symbol::Ident;

    use super::{
        AliasMap, Arg, BaseTy, BinOp, Expr, ExprKind, FnSig, Indices, Path, RefineArg, Ty, TyKind,
    };

    /// `expand_sig(aliases, sig)` replaces all the alias-applications in `sig`
    /// with the corresponding type definitions from `aliases` (if any).
    pub fn expand_sig(aliases: &AliasMap, fn_sig: FnSig) -> Result<FnSig, ErrorGuaranteed> {
        Ok(FnSig {
            params: fn_sig.params,
            args: expand_args(aliases, fn_sig.args)?,
            returns: fn_sig.returns.as_ref().map(|ty| expand_ty(aliases, ty)),
            ensures: expand_locs(aliases, fn_sig.ensures),
            requires: fn_sig.requires,
            span: fn_sig.span,
        })
    }

    fn expand_args(aliases: &AliasMap, args: Vec<Arg>) -> Result<Vec<Arg>, ErrorGuaranteed> {
        args.into_iter()
            .map(|arg| expand_arg(aliases, arg))
            .collect()
    }

    fn expand_arg(aliases: &AliasMap, arg: Arg) -> Result<Arg, ErrorGuaranteed> {
        match arg {
            Arg::Alias(x, path, indices) => {
                let span = path.span;
                match expand_alias_path(aliases, &path, &indices) {
                    Some(TyKind::Exists {
                        bind: e_bind,
                        base: BaseTy::Path(e_path),
                        pred: e_pred,
                    }) => Ok(expand_arg_exists(x, e_path, e_bind, e_pred)),
                    _ => {
                        Ok(Arg::Ty(
                            None,
                            Ty {
                                kind: TyKind::Indexed { base: BaseTy::Path(path), indices },
                                span,
                            },
                        ))
                    }
                }
            }
            Arg::Constr(x, path, e) => Ok(Arg::Constr(x, expand_path(aliases, &path), e)),
            Arg::Ty(x, ty) => Ok(Arg::Ty(x, expand_ty(aliases, &ty))),
            Arg::StrgRef(x, ty) => Ok(Arg::StrgRef(x, expand_ty(aliases, &ty))),
        }
    }

    fn expand_arg_exists(x: Ident, e_path: Path, e_bind: Ident, e_pred: Expr) -> Arg {
        let subst = mk_sub1(e_bind, x);
        let x_pred = subst_expr(&subst, &e_pred);
        Arg::Constr(x, e_path, x_pred)
    }

    fn expand_alias_path(aliases: &AliasMap, path: &Path, indices: &Indices) -> Option<TyKind> {
        let id = path.ident;
        if let Some(alias) = aliases.get(&id) {
            let subst = mk_sub(&alias.args, &indices.indices);
            let ty = subst_ty(&subst, &alias.defn);
            return Some(ty.kind);
        }
        None
    }

    fn expand_alias(aliases: &AliasMap, base: &BaseTy, indices: &Indices) -> Option<TyKind> {
        if let BaseTy::Path(path) = base {
            return expand_alias_path(aliases, path, indices);
        }
        None
    }

    fn expand_path(aliases: &AliasMap, path: &Path) -> Path {
        Path {
            ident: path.ident,
            args: path.args.iter().map(|t| expand_ty(aliases, t)).collect(),
            span: path.span,
        }
    }

    fn expand_base(aliases: &AliasMap, base: &BaseTy) -> BaseTy {
        match base {
            BaseTy::Path(path) => BaseTy::Path(expand_path(aliases, path)),
            BaseTy::Array(ty, len) => BaseTy::Array(Box::new(expand_ty(aliases, ty)), *len),
            BaseTy::Slice(ty) => BaseTy::Slice(Box::new(expand_ty(aliases, ty))),
        }
    }

    fn expand_ty(aliases: &AliasMap, ty: &Ty) -> Ty {
        let kind = expand_kind(aliases, &ty.kind, ty.span);
        Ty { kind, span: ty.span }
    }

    fn expand_kind(aliases: &AliasMap, k: &TyKind, span: crate::Span) -> TyKind {
        match k {
            TyKind::Base(base) => {
                let indices = Indices { indices: vec![], span };
                match expand_alias(aliases, base, &indices) {
                    Some(k) => k,
                    None => TyKind::Base(expand_base(aliases, base)),
                }
            }
            TyKind::Exists { bind, base, pred } => {
                TyKind::Exists { bind: *bind, base: expand_base(aliases, base), pred: pred.clone() }
            }
            TyKind::Indexed { base, indices } => {
                match expand_alias(aliases, base, indices) {
                    Some(k) => k,
                    None => {
                        TyKind::Indexed {
                            base: expand_base(aliases, base),
                            indices: indices.clone(),
                        }
                    }
                }
            }
            TyKind::Ref(rk, t) => TyKind::Ref(*rk, Box::new(expand_ty(aliases, t))),
            TyKind::Constr(pred, t) => {
                TyKind::Constr(pred.clone(), Box::new(expand_ty(aliases, t)))
            }
            TyKind::Tuple(tys) => {
                TyKind::Tuple(tys.iter().map(|t| expand_ty(aliases, t)).collect())
            }
        }
    }

    fn _and(e1: Expr, e2: Expr) -> Expr {
        let span = e1.span;
        let kind = ExprKind::BinaryOp(BinOp::And, Box::new([e1, e2]));
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

    fn mk_sub(src: &Vec<Ident>, dst: &Vec<RefineArg>) -> Subst {
        assert_eq!(src.len(), dst.len(), "mk_sub: invalid args");
        let mut res = HashMap::new();
        for (src_id, dst_ix) in iter::zip(src, dst) {
            match dst_ix {
                RefineArg::Expr(e) => {
                    res.insert(*src_id, e.clone());
                }
                RefineArg::Bind(..) => panic!("cannot use binder in type alias"),
                RefineArg::Abs(..) => panic!("cannot use `RefineArg::Abs` in type alias"),
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
            ExprKind::BinaryOp(op, box [e1, e2]) => {
                Expr {
                    kind: ExprKind::BinaryOp(
                        *op,
                        Box::new([subst_expr(subst, e1), subst_expr(subst, e2)]),
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
            ExprKind::IfThenElse(box [p, e1, e2]) => {
                Expr {
                    kind: ExprKind::IfThenElse(Box::new([
                        subst_expr(subst, p),
                        subst_expr(subst, e1),
                        subst_expr(subst, e2),
                    ])),
                    span: e.span,
                }
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
            indices.push(subst_arg(subst, i));
        }
        Indices { indices, span: i_indices.span }
    }

    fn subst_arg(subst: &Subst, arg: &RefineArg) -> RefineArg {
        match arg {
            RefineArg::Expr(e) => RefineArg::Expr(subst_expr(subst, e)),
            RefineArg::Bind(..) | RefineArg::Abs(..) => arg.clone(),
        }
    }

    fn subst_base(subst: &Subst, base: &BaseTy) -> BaseTy {
        match base {
            BaseTy::Path(path) => BaseTy::Path(subst_path(subst, path)),
            BaseTy::Array(ty, len) => BaseTy::Array(Box::new(subst_ty(subst, ty)), *len),
            BaseTy::Slice(ty) => BaseTy::Slice(Box::new(subst_ty(subst, ty))),
        }
    }

    fn subst_tykind(subst: &Subst, k: &TyKind) -> TyKind {
        match k {
            TyKind::Base(base) => TyKind::Base(subst_base(subst, base)),
            TyKind::Indexed { base, indices } => {
                TyKind::Indexed {
                    base: subst_base(subst, base),
                    indices: subst_indices(subst, indices),
                }
            }
            TyKind::Exists { bind, base, pred } => {
                TyKind::Exists {
                    bind: *bind,
                    base: subst_base(subst, base),
                    pred: subst_expr(subst, pred),
                }
            }
            TyKind::Ref(rk, t) => TyKind::Ref(*rk, Box::new(subst_ty(subst, t))),
            TyKind::Constr(pred, t) => {
                TyKind::Constr(subst_expr(subst, pred), Box::new(subst_ty(subst, t)))
            }
            TyKind::Tuple(tys) => TyKind::Tuple(tys.iter().map(|t| subst_ty(subst, t)).collect()),
        }
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use rustc_span::Span;
    #[derive(Diagnostic)]
    #[diag(parse::invalid_alias_application, code = "FLUX")]
    pub struct InvalidAliasApplication {
        #[primary_span]
        pub span: Span,
    }
}
