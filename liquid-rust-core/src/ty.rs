use liquid_rust_common::index::newtype_index;
pub use liquid_rust_syntax::ast::BinOp;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
pub use rustc_middle::ty::{IntTy, ParamTy, UintTy};
use rustc_span::{Span, Symbol};

pub struct AdtDefs {
    map: FxHashMap<LocalDefId, AdtDef>,
}

#[derive(Debug)]
pub enum AdtDef {
    Transparent { refined_by: Vec<Param>, fields: Vec<Ty> },
    Opaque { refined_by: Vec<Param> },
}

#[derive(Debug)]
pub struct FnSig {
    pub params: Vec<Param>,
    pub requires: Vec<(Name, Ty)>,
    pub args: Vec<Ty>,
    pub ret: Ty,
    pub ensures: Vec<(Name, Ty)>,
}

#[derive(Debug)]
pub enum Ty {
    Refine(BaseTy, Refine),
    Exists(BaseTy, Pred),
    StrgRef(Name),
    WeakRef(Box<Ty>),
    ShrRef(Box<Ty>),
    Param(ParamTy),
}

#[derive(Debug)]
pub struct Refine {
    pub exprs: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug)]
pub enum Pred {
    Infer,
    Expr(Expr),
}

#[derive(Debug)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Adt(DefId, Vec<Ty>),
}

#[derive(Debug)]
pub struct Param {
    pub name: Ident,
    pub sort: Sort,
    pub pred: Expr,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Sort {
    Bool,
    Int,
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Option<Span>,
}

#[derive(Debug)]
pub enum ExprKind {
    Var(Var, Symbol, Span),
    Literal(Lit),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum Var {
    Bound,
    Free(Name),
}

#[derive(Clone, Copy, Debug)]
pub enum Lit {
    Int(i128),
    Bool(bool),
}

#[derive(Debug, Clone, Copy)]
pub struct Ident {
    pub name: Name,
    pub source_info: (Span, Symbol),
}

newtype_index! {
    pub struct Name {
        DEBUG_FORMAT = "x{}",
    }
}

impl BaseTy {
    /// Returns `true` if the base ty is [`Bool`].
    ///
    /// [`Bool`]: BaseTy::Bool
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }
}

impl Expr {
    pub const TRUE: Expr = Expr { kind: ExprKind::Literal(Lit::TRUE), span: None };
}

impl Pred {
    pub const TRUE: Pred = Pred::Expr(Expr::TRUE);
}

impl Lit {
    pub const TRUE: Lit = Lit::Bool(true);
}

impl AdtDef {
    pub fn refined_by(&self) -> &[Param] {
        match self {
            Self::Transparent { refined_by, .. } | Self::Opaque { refined_by } => refined_by,
        }
    }
}

impl AdtDefs {
    pub fn get(&self, did: LocalDefId) -> Option<&AdtDef> {
        self.map.get(&did)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&LocalDefId, &AdtDef)> {
        self.map.iter()
    }
}

impl FromIterator<(LocalDefId, AdtDef)> for AdtDefs {
    fn from_iter<T: IntoIterator<Item = (LocalDefId, AdtDef)>>(iter: T) -> Self {
        AdtDefs { map: iter.into_iter().collect() }
    }
}

impl IntoIterator for AdtDefs {
    type Item = (LocalDefId, AdtDef);

    type IntoIter = std::collections::hash_map::IntoIter<LocalDefId, AdtDef>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}
