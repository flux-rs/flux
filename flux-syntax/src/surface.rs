use std::fmt;

pub use rustc_ast::token::{Lit, LitKind};
use rustc_hir::def_id::{DefId, LocalDefId};
pub use rustc_middle::ty::{FloatTy, IntTy, ParamTy, TyCtxt, UintTy};
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

pub type AliasMap = rustc_hash::FxHashMap<Ident, Alias>;

#[derive(Debug)]
pub struct SortDecl {
    pub name: Ident,
}

#[derive(Debug)]
pub enum Item {
    Qualifier(Qualifier),
    Defn(Defn),
    Uif(UifDef),
    SortDecl(SortDecl),
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: Ident,
    pub args: Vec<RefineParam>,
    pub expr: Expr,
    pub span: Span,
    pub global: bool,
}

#[derive(Debug)]
pub enum Def {
    Defn(Defn),
    UifDef(UifDef),
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
    pub args: RefinedBy,
    /// output sort
    pub sort: Sort,
    /// definition source position
    pub span: Span,
}

#[derive(Debug)]
pub struct Alias<R = ()> {
    pub name: Ident,
    pub args: Vec<Ident>,
    pub defn: Ty<R>,
    pub span: Span,
}

#[derive(Debug)]
pub struct StructDef<R = ()> {
    pub def_id: LocalDefId,
    pub refined_by: Option<RefinedBy>,
    pub fields: Vec<Option<Ty<R>>>,
    pub opaque: bool,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct EnumDef<R = ()> {
    pub def_id: LocalDefId,
    pub refined_by: Option<RefinedBy>,
    pub variants: Vec<VariantDef<R>>,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct VariantDef<R = ()> {
    pub fields: Vec<Ty<R>>,
    pub ret: VariantRet<R>,
    pub span: Span,
}

#[derive(Debug)]
pub struct VariantRet<R = ()> {
    pub path: Path<R>,
    /// Binders are not allowed at this position, but we parse this as a list of indices
    /// for better error reporting.
    pub indices: Indices,
}

#[derive(Debug, Default)]
pub struct RefinedBy {
    pub params: Vec<RefineParam>,
    pub span: Span,
}
#[derive(Debug, Default)]
pub struct QualNames {
    pub names: Vec<Ident>,
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
pub struct FnSig<R = ()> {
    /// List of explicit refinement parameters
    pub params: Vec<RefineParam>,
    /// example: `requires n > 0`
    pub requires: Option<Expr>,
    /// example: `i32<@n>`
    pub args: Vec<Arg<R>>,
    /// example `i32{v:v >= 0}`
    pub returns: Option<Ty<R>>,
    /// example: `*x: i32{v. v = n+1}`
    pub ensures: Vec<(Ident, Ty<R>)>,
    /// source span
    pub span: Span,
}

#[derive(Debug)]
pub enum Arg<R = ()> {
    /// example `a: i32{a > 0}`
    Constr(Ident, Path<R>, Expr),
    /// example `x: nat` or `x: lb[0]`
    Alias(Ident, Path<R>, Indices),
    /// example `v: &strg i32`
    StrgRef(Ident, Ty<R>),
    /// A type with an optional binder, e.g, `i32`, `x: i32` or `x: i32{v : v > 0}`.
    /// The binder has a different meaning depending on the type.
    Ty(Option<Ident>, Ty<R>),
}

#[derive(Debug)]
pub struct Ty<R = ()> {
    pub kind: TyKind<R>,
    pub span: Span,
}

#[derive(Debug)]
pub enum BaseTy<R = ()> {
    Path(Path<R>),
    Slice(Box<Ty<R>>),
}

#[derive(Debug)]
pub enum TyKind<R = ()> {
    /// ty
    Base(BaseTy<R>),
    /// `t[e]`
    Indexed {
        bty: BaseTy<R>,
        indices: Indices,
    },
    /// ty{b:e}
    Exists {
        bind: Ident,
        bty: BaseTy<R>,
        pred: Expr,
    },
    /// Mutable or shared reference
    Ref(RefKind, Box<Ty<R>>),
    /// Constrained type: an exists without binder
    Constr(Expr, Box<Ty<R>>),
    Tuple(Vec<Ty<R>>),
    Array(Box<Ty<R>>, ArrayLen),
}

#[derive(Debug, Clone, Copy)]
pub struct ArrayLen {
    pub val: usize,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Indices {
    pub indices: Vec<RefineArg>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum RefineArg {
    /// `@n` or `#n`, the span corresponds to the span of the identifier plus the binder token (`@` or `#`)
    Bind(Ident, BindKind, Span),
    Expr(Expr),
    Abs(Vec<Ident>, Expr, Span),
}

#[derive(Debug, Clone, Copy)]
pub enum BindKind {
    At,
    Pound,
}

#[derive(Debug)]
pub struct Path<R = ()> {
    pub segments: Vec<Ident>,
    pub args: Vec<Ty<R>>,
    pub span: Span,
    pub res: R,
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
    UnaryOp(UnOp, Box<Expr>),
    App(Ident, Vec<Expr>),
    IfThenElse(Box<[Expr; 3]>),
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
    Div,
}

#[derive(Copy, Clone, Debug)]
pub enum UnOp {
    Not,
    Neg,
}

impl BindKind {
    pub fn token_str(&self) -> &'static str {
        match self {
            BindKind::At => "@",
            BindKind::Pound => "#",
        }
    }
}

impl RefinedBy {
    pub const DUMMY: &RefinedBy = &RefinedBy { params: vec![], span: rustc_span::DUMMY_SP };
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
            BinOp::Div => write!(f, "/"),
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
                        bty: BaseTy::Path(e_path),
                        pred: e_pred,
                    }) => Ok(expand_arg_exists(x, e_path, e_bind, e_pred)),
                    _ => {
                        Ok(Arg::Ty(
                            None,
                            Ty { kind: TyKind::Indexed { bty: BaseTy::Path(path), indices }, span },
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
        if let [id] = &path.segments[..]
           && let Some(alias) = aliases.get(id)
        {
            let subst = mk_sub(&alias.args, &indices.indices);
            let ty = subst_ty(&subst, &alias.defn);
            return Some(ty.kind);
        }
        None
    }

    fn expand_alias(aliases: &AliasMap, bty: &BaseTy, indices: &Indices) -> Option<TyKind> {
        if let BaseTy::Path(path) = bty {
            return expand_alias_path(aliases, path, indices);
        }
        None
    }

    fn expand_path(aliases: &AliasMap, path: &Path) -> Path {
        Path {
            segments: path.segments.clone(),
            args: path.args.iter().map(|t| expand_ty(aliases, t)).collect(),
            span: path.span,
            res: path.res,
        }
    }

    fn expand_bty(aliases: &AliasMap, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Path(path) => BaseTy::Path(expand_path(aliases, path)),
            BaseTy::Slice(ty) => BaseTy::Slice(Box::new(expand_ty(aliases, ty))),
        }
    }

    fn expand_ty(aliases: &AliasMap, ty: &Ty) -> Ty {
        let kind = expand_kind(aliases, &ty.kind, ty.span);
        Ty { kind, span: ty.span }
    }

    fn expand_kind(aliases: &AliasMap, k: &TyKind, span: crate::Span) -> TyKind {
        match k {
            TyKind::Base(bty) => {
                let indices = Indices { indices: vec![], span };
                match expand_alias(aliases, bty, &indices) {
                    Some(k) => k,
                    None => TyKind::Base(expand_bty(aliases, bty)),
                }
            }
            TyKind::Exists { bind, bty: base, pred } => {
                TyKind::Exists { bind: *bind, bty: expand_bty(aliases, base), pred: pred.clone() }
            }
            TyKind::Indexed { bty, indices } => {
                match expand_alias(aliases, bty, indices) {
                    Some(k) => k,
                    None => {
                        TyKind::Indexed { bty: expand_bty(aliases, bty), indices: indices.clone() }
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
            TyKind::Array(ty, len) => TyKind::Array(Box::new(expand_ty(aliases, ty)), *len),
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
            ExprKind::UnaryOp(op, e) => {
                Expr { kind: ExprKind::UnaryOp(*op, Box::new(subst_expr(subst, e))), span: e.span }
            }
            ExprKind::Dot(e, fld) => {
                Expr { kind: ExprKind::Dot(Box::new(subst_expr(subst, e)), *fld), span: e.span }
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
        Path { segments: p.segments.clone(), args, span: p.span, res: p.res }
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

    fn subst_bty(subst: &Subst, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Path(path) => BaseTy::Path(subst_path(subst, path)),
            BaseTy::Slice(ty) => BaseTy::Slice(Box::new(subst_ty(subst, ty))),
        }
    }

    fn subst_tykind(subst: &Subst, k: &TyKind) -> TyKind {
        match k {
            TyKind::Base(bty) => TyKind::Base(subst_bty(subst, bty)),
            TyKind::Indexed { bty: base, indices } => {
                TyKind::Indexed {
                    bty: subst_bty(subst, base),
                    indices: subst_indices(subst, indices),
                }
            }
            TyKind::Exists { bind, bty, pred } => {
                TyKind::Exists {
                    bind: *bind,
                    bty: subst_bty(subst, bty),
                    pred: subst_expr(subst, pred),
                }
            }
            TyKind::Ref(rk, t) => TyKind::Ref(*rk, Box::new(subst_ty(subst, t))),
            TyKind::Constr(pred, t) => {
                TyKind::Constr(subst_expr(subst, pred), Box::new(subst_ty(subst, t)))
            }
            TyKind::Tuple(tys) => TyKind::Tuple(tys.iter().map(|t| subst_ty(subst, t)).collect()),
            TyKind::Array(ty, len) => TyKind::Array(Box::new(subst_ty(subst, ty)), *len),
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
