pub mod visit;

use std::fmt;

pub use rustc_ast::{
    token::{Lit, LitKind},
    Mutability,
};
pub use rustc_span::symbol::Ident;
use rustc_span::{def_id::DefId, symbol::kw, Span};

use crate::surface::visit::Visitor;

/// A [`NodeId`] is a unique identifier we assign to some AST nodes to be able to attach information
/// to them. For example, to assign a resolution to a [`Path`]. The [`NodeId`] is unique within a crate.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct NodeId(pub(super) usize);

impl NodeId {
    pub fn as_usize(&self) -> usize {
        self.0
    }
}

#[derive(Debug)]
pub struct SortDecl {
    pub name: Ident,
}

#[derive(Debug)]
pub enum Item {
    Qualifier(Qualifier),
    FuncDef(FuncDef),
    SortDecl(SortDecl),
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: Ident,
    pub args: Vec<RefineParam>,
    pub expr: Expr,
    pub span: Span,
    pub global: bool,
    pub node_id: NodeId,
}

/// A global function definition. It can be either an uninterpreted function or a *syntactic abstraction*,
/// i.e., a function with a body.
#[derive(Debug)]
pub struct FuncDef {
    pub name: Ident,
    pub sort_vars: Vec<Ident>,
    pub args: Vec<RefineParam>,
    pub output: Sort,
    /// Body of the function. If not present this definition corresponds to an uninterpreted function.
    pub body: Option<Expr>,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub predicates: Vec<WhereBoundPredicate>,
    pub span: Span,
}

#[derive(Debug)]
pub struct GenericParam {
    pub name: Ident,
    pub kind: GenericParamKind,
}

#[derive(Debug)]
pub enum GenericParamKind {
    Type,
    Spl,
    Base,
    Refine { sort: Sort },
}

#[derive(Debug)]
pub struct TyAlias {
    pub ident: Ident,
    pub generics: Generics,
    pub refined_by: RefinedBy,
    pub ty: Ty,
    pub node_id: NodeId,
    pub span: Span,
}

#[derive(Debug)]
pub struct StructDef {
    pub generics: Option<Generics>,
    pub refined_by: Option<RefinedBy>,
    pub fields: Vec<Option<Ty>>,
    pub opaque: bool,
    pub invariants: Vec<Expr>,
    pub node_id: NodeId,
    /// Whether the struct is an extern spec for some [DefId]
    pub extern_id: Option<DefId>,
}

impl StructDef {
    /// Whether the struct contains any path that needs to be resolved.
    pub fn needs_resolving(&self) -> bool {
        self.fields.iter().any(Option::is_some)
    }
}

#[derive(Debug)]
pub struct EnumDef {
    pub generics: Option<Generics>,
    pub refined_by: Option<RefinedBy>,
    pub variants: Vec<Option<VariantDef>>,
    pub invariants: Vec<Expr>,
    pub node_id: NodeId,
    /// Whether the enum is an extern spec for some [DefId]
    pub extern_id: Option<DefId>,
}

impl EnumDef {
    /// Whether the enum contains any path that needs to be resolved.
    pub fn needs_resolving(&self) -> bool {
        self.variants.iter().any(Option::is_some)
    }
}

#[derive(Debug)]
pub struct VariantDef {
    pub fields: Vec<Ty>,
    pub ret: Option<VariantRet>,
    pub node_id: NodeId,
    pub span: Span,
}

#[derive(Debug)]
pub struct VariantRet {
    pub path: Path,
    /// Binders are not allowed at this position, but we parse this as a list of indices
    /// for better error reporting.
    pub indices: Indices,
}

#[derive(Debug, Default)]
pub struct RefinedBy {
    pub index_params: Vec<RefineParam>,
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
    pub span: Span,
}

#[derive(Debug)]
pub enum Sort {
    /// A _base_ sort, e.g., `int` or `bool`.
    Base(BaseSort),
    /// A _function_ sort of the form `(bi,...) -> bo` where `bi..` and `bo`
    /// are all base sorts.
    Func {
        inputs: Vec<BaseSort>,
        output: BaseSort,
    },
    Infer,
}

#[derive(Debug, Clone)]
pub enum BaseSort {
    /// a _base_ sort, e.g. `int` or `bool`
    Ident(Ident),
    /// a bitvector sort, e.g., BitVec(32)
    BitVec(usize),
    /// a sort-constructor application, e.g., `Set<int>`
    App(Ident, Vec<BaseSort>),
}

#[derive(Debug)]
pub struct ConstSig {
    pub span: Span,
}

pub struct Impl {
    pub generics: Option<Generics>,
    pub assoc_predicates: Vec<ImplAssocPredicate>,
}

#[derive(Debug)]
pub struct ImplAssocPredicate {
    pub name: Ident,
    pub params: Vec<RefineParam>,
    pub body: Expr,
    pub span: Span,
    pub node_id: NodeId,
}

pub struct Trait {
    pub generics: Option<Generics>,
    pub assoc_predicates: Vec<TraitAssocPredicate>,
}

#[derive(Debug)]
pub struct TraitAssocPredicate {
    pub name: Ident,
    pub sort: Sort,
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct FnSpec {
    pub fn_sig: Option<FnSig>,
    pub trusted: bool,
    pub qual_names: Option<QualNames>,
}

#[derive(Debug)]
pub struct FnSig {
    pub asyncness: Async,
    pub generics: Generics,
    /// example: `requires n > 0`
    pub requires: Option<Expr>,
    /// example: `i32<@n>`
    pub args: Vec<Arg>,
    pub output: FnOutput,
    /// source span
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct FnOutput {
    /// example `i32{v:v >= 0}`
    pub returns: FnRetTy,
    /// example: `*x: i32{v. v = n+1}` or just `x > 10`
    pub ensures: Vec<Constraint>,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub enum Constraint {
    /// A type constraint on a location
    Type(Ident, Ty, NodeId),
    /// A predicate that needs to hold
    Pred(Expr),
}

#[derive(Debug)]
pub enum FnRetTy {
    Default(Span),
    Ty(Ty),
}

#[derive(Debug, Copy, Clone)]
pub enum Async {
    Yes { node_id: NodeId, span: Span },
    No,
}

#[derive(Debug)]
pub struct WhereBoundPredicate {
    pub span: Span,
    pub bounded_ty: Ty,
    pub bounds: GenericBounds,
}

pub type GenericBounds = Vec<TraitRef>;

#[derive(Debug)]
pub struct TraitRef {
    pub path: Path,
}

#[derive(Debug)]
pub enum Arg {
    /// example `a: i32{a > 0}`
    Constr(Ident, Path, Expr),
    /// example `v: &strg i32`
    StrgRef(Ident, Ty, NodeId),
    /// A type with an optional binder, e.g, `i32`, `x: i32` or `x: i32{v: v > 0}`.
    /// The binder has a different meaning depending on the type.
    Ty(Option<Ident>, Ty),
}

#[derive(Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub node_id: NodeId,
    pub span: Span,
}

#[derive(Debug)]
pub struct AliasPred {
    pub trait_id: Path,
    pub name: Ident,
    pub generic_args: Vec<GenericArg>,
    // pub refine_args: Vec<RefineArg>,
}

#[derive(Debug)]
pub enum TyKind {
    /// ty
    Base(BaseTy),
    /// `B[r]`
    Indexed {
        bty: BaseTy,
        indices: Indices,
    },
    /// B{v: r}
    Exists {
        bind: Ident,
        bty: BaseTy,
        pred: Pred,
    },
    GeneralExists {
        params: Vec<RefineParam>,
        ty: Box<Ty>,
        pred: Option<Expr>,
    },
    /// Mutable or shared reference
    Ref(Mutability, Box<Ty>),
    /// Constrained type: an exists without binder
    Constr(Pred, Box<Ty>),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, ArrayLen),
    /// The `NodeId` is used to resolve the type to a corresponding `OpaqueTy`
    ImplTrait(NodeId, GenericBounds),
}

#[derive(Debug)]
pub struct Pred {
    pub kind: PredKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum PredKind {
    Expr(Expr),
    Alias(AliasPred, Vec<RefineArg>),
}

impl Ty {
    pub fn as_bty(&self) -> Option<&BaseTy> {
        match &self.kind {
            TyKind::Base(bty) | TyKind::Indexed { bty, .. } | TyKind::Exists { bty, .. } => {
                Some(bty)
            }
            TyKind::GeneralExists { ty, .. } | TyKind::Constr(_, ty) => ty.as_bty(),
            TyKind::Ref(_, _)
            | TyKind::Tuple(_)
            | TyKind::Array(_, _)
            | TyKind::ImplTrait(_, _) => None,
        }
    }

    pub fn is_refined(&self) -> bool {
        struct IsRefinedVisitor {
            is_refined: bool,
        }
        let mut vis = IsRefinedVisitor { is_refined: false };
        impl visit::Visitor for IsRefinedVisitor {
            fn visit_ty(&mut self, ty: &Ty) {
                if !matches!(ty.kind, TyKind::Base(_)) {
                    self.is_refined = true;
                }
                visit::walk_ty(self, ty);
            }
        }
        vis.visit_ty(self);
        vis.is_refined
    }
}
#[derive(Debug)]
pub struct BaseTy {
    pub kind: BaseTyKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum BaseTyKind {
    Path(Path),
    Slice(Box<Ty>),
}

#[derive(Debug, Clone, Copy)]
pub struct ArrayLen {
    pub val: usize,
    pub span: Span,
}

#[derive(Debug)]
pub struct Indices {
    pub indices: Vec<RefineArg>,
    pub span: Span,
}

#[derive(Debug)]
pub enum RefineArg {
    /// `@n` or `#n`, the span corresponds to the span of the identifier plus the binder token (`@` or `#`)
    Bind(Ident, BindKind, Span),
    Expr(Expr),
    Abs(Vec<RefineParam>, Expr, NodeId, Span),
}

#[derive(Debug, Clone, Copy)]
pub enum BindKind {
    At,
    Pound,
}

#[derive(Debug)]
pub struct Path {
    pub segments: Vec<Ident>,
    pub generics: Vec<GenericArg>,
    pub refine: Vec<RefineArg>,
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct GenericArg {
    pub kind: GenericArgKind,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub enum GenericArgKind {
    Type(Ty),
    Constraint(Ident, Ty),
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub node_id: NodeId,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    QPath(QPathExpr),
    Dot(QPathExpr, Ident),
    Literal(Lit),
    BinaryOp(BinOp, Box<[Expr; 2]>),
    UnaryOp(UnOp, Box<Expr>),
    App(Ident, Vec<Expr>),
    IfThenElse(Box<[Expr; 3]>),
}

#[derive(Debug, Clone)]
pub struct QPathExpr {
    pub segments: Vec<Ident>,
    pub node_id: NodeId,
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
    Div,
}

#[derive(Copy, Clone, Debug)]
pub enum UnOp {
    Not,
    Neg,
}

impl Path {
    pub fn is_hole(&self) -> bool {
        if let [segment] = &self.segments[..] {
            segment.name == kw::Underscore && self.generics.is_empty() && self.refine.is_empty()
        } else {
            false
        }
    }
}

impl BindKind {
    pub fn token_str(&self) -> &'static str {
        match self {
            BindKind::At => "@",
            BindKind::Pound => "#",
        }
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
