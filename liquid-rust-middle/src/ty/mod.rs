pub mod fold;
pub mod lowering;
pub mod subst;

use std::{fmt, lazy::SyncOnceCell};

use itertools::Itertools;
use liquid_rust_common::index::IndexVec;

pub use liquid_rust_fixpoint::{BinOp, Constant, KVid, UnOp};
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
pub use rustc_middle::ty::{FloatTy, IntTy, UintTy};
use rustc_middle::{
    mir::{Field, Local},
    ty::ParamTy,
};
pub use rustc_target::abi::VariantIdx;

pub use crate::core::RefKind;
use crate::intern::{impl_internable, Interned, List};
use subst::Subst;

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct AdtDef(Interned<AdtDefData>);

#[derive(Eq, PartialEq, Hash)]
pub struct AdtDefData {
    refined_by: Vec<Param>,
    def_id: DefId,
    kind: AdtDefKind,
}

#[derive(Eq, PartialEq, Hash)]
enum AdtDefKind {
    Transparent { variants: IndexVec<VariantIdx, VariantDef> },
    Opaque,
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct VariantDef {
    pub fields: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct Binders<T> {
    params: List<Param>,
    value: T,
}

pub type PolySig = Binders<FnSig>;

#[derive(Clone)]
pub struct FnSig {
    requires: List<Constr>,
    args: List<Ty>,
    ret: Ty,
    ensures: List<Constr>,
}

pub type Constrs = List<Constr>;

#[derive(Clone, Eq, PartialEq, Hash)]
pub enum Constr {
    Type(Path, Ty),
    Pred(Expr),
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: String,
    pub args: Vec<(Name, Sort)>,
    pub expr: Expr,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Param {
    pub name: Name,
    pub sort: Sort,
}

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TyKind {
    Indexed(BaseTy, List<Index>),
    Exists(BaseTy, Pred),
    Tuple(List<Ty>),
    Float(FloatTy),
    Uninit,
    Ptr(Path),
    Ref(RefKind, Ty),
    Param(ParamTy),
    Never,
    /// Used internally to represent result of `discriminant` RVal
    Discr,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Index {
    pub expr: Expr,
    pub is_binder: bool,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Path {
    pub loc: Loc,
    projection: List<Field>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Loc {
    Local(Local),
    Free(Name),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Adt(AdtDef, Substs),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Substs(List<Ty>);

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Pred {
    Hole,
    Kvars(List<KVar>),
    Expr(Expr),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct KVar(pub KVid, pub List<Expr>);

pub type Sort = Interned<SortS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SortS {
    kind: SortKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum SortKind {
    Int,
    Bool,
    Loc,
    Tuple(Vec<Sort>),
}

pub type Expr = Interned<ExprS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ExprS {
    kind: ExprKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ExprKind {
    FreeVar(Name),
    BoundVar(u32),
    Local(Local),
    Constant(Constant),
    BinaryOp(BinOp, Expr, Expr),
    UnaryOp(UnOp, Expr),
    TupleProj(Expr, u32),
    Tuple(List<Expr>),
    PathProj(Expr, Field),
}

newtype_index! {
    pub struct Name {
        DEBUG_FORMAT = "a{}",
    }
}

impl<T> Binders<T> {
    pub fn new<P>(params: P, value: T) -> Binders<T>
    where
        List<Param>: From<P>,
    {
        Binders { params: Interned::from(params), value }
    }

    pub fn params(&self) -> &[Param] {
        &self.params
    }

    pub fn value(&self) -> &T {
        &self.value
    }
}

impl FnSig {
    pub fn new<A, B, C>(requires: A, args: B, ret: Ty, ensures: C) -> Self
    where
        List<Constr>: From<A>,
        List<Ty>: From<B>,
        List<Constr>: From<C>,
    {
        FnSig {
            requires: Interned::from(requires),
            args: Interned::from(args),
            ret,
            ensures: Interned::from(ensures),
        }
    }
    pub fn requires(&self) -> &Constrs {
        &self.requires
    }

    pub fn args(&self) -> &[Ty] {
        &self.args
    }

    pub fn ret(&self) -> &Ty {
        &self.ret
    }

    pub fn ensures(&self) -> &Constrs {
        &self.ensures
    }
}

impl AdtDef {
    pub fn opaque(def_id: DefId, refined_by: Vec<Param>) -> Self {
        let kind = AdtDefKind::Opaque;
        AdtDef(Interned::new(AdtDefData { def_id, kind, refined_by }))
    }

    pub fn transparent(
        def_id: DefId,
        refined_by: Vec<Param>,
        variants: IndexVec<VariantIdx, VariantDef>,
    ) -> Self {
        let kind = AdtDefKind::Transparent { variants };
        AdtDef(Interned::new(AdtDefData { def_id, kind, refined_by }))
    }

    pub fn def_id(&self) -> DefId {
        self.0.def_id
    }

    pub fn refined_by(&self) -> &[Param] {
        &self.0.refined_by
    }

    pub fn sorts(&self) -> Vec<Sort> {
        self.refined_by()
            .iter()
            .map(|param| param.sort.clone())
            .collect()
    }

    pub fn unfold(
        &self,
        substs: &Substs,
        indices: &[Index],
        variant_idx: VariantIdx,
    ) -> Option<IndexVec<Field, Ty>> {
        let fields = &self.variants()?[variant_idx].fields;
        let mut subst = Subst::with_type_substs(substs.as_slice());
        debug_assert_eq!(indices.len(), self.refined_by().len());
        for (idx, param) in indices.iter().zip(self.refined_by()) {
            subst.insert(param.name, idx.expr.clone());
        }
        Some(fields.iter().map(|ty| subst.subst_ty(ty)).collect())
    }

    pub fn variants(&self) -> Option<&IndexVec<VariantIdx, VariantDef>> {
        match self.kind() {
            AdtDefKind::Transparent { variants, .. } => Some(variants),
            AdtDefKind::Opaque { .. } => None,
        }
    }

    fn kind(&self) -> &AdtDefKind {
        &self.0.kind
    }
}

impl VariantDef {
    pub fn new(fields: Vec<Ty>) -> Self {
        VariantDef { fields }
    }
}

impl Ty {
    pub fn ptr(path: impl Into<Path>) -> Ty {
        TyKind::Ptr(path.into()).intern()
    }

    pub fn mk_ref(mode: RefKind, ty: Ty) -> Ty {
        TyKind::Ref(mode, ty).intern()
    }

    pub fn tuple(tys: impl Into<List<Ty>>) -> Ty {
        TyKind::Tuple(tys.into()).intern()
    }

    pub fn uninit() -> Ty {
        TyKind::Uninit.intern()
    }

    pub fn indexed<T>(bty: BaseTy, indices: T) -> Ty
    where
        List<Index>: From<T>,
    {
        TyKind::Indexed(bty, Interned::from(indices)).intern()
    }

    pub fn exists(bty: BaseTy, pred: impl Into<Pred>) -> Ty {
        TyKind::Exists(bty, pred.into()).intern()
    }

    pub fn float(float_ty: FloatTy) -> Ty {
        TyKind::Float(float_ty).intern()
    }

    pub fn param(param: ParamTy) -> Ty {
        TyKind::Param(param).intern()
    }

    pub fn unit() -> Ty {
        Ty::tuple(vec![])
    }

    pub fn never() -> Ty {
        TyKind::Never.intern()
    }

    pub fn discr() -> Ty {
        TyKind::Discr.intern()
    }
}

impl TyKind {
    fn intern(self) -> Ty {
        Interned::new(TyS { kind: self })
    }
}

impl TyS {
    pub fn kind(&self) -> &TyKind {
        &self.kind
    }

    pub fn is_uninit(&self) -> bool {
        matches!(self.kind(), TyKind::Uninit)
    }

    pub fn unfold(&self, variant_idx: VariantIdx) -> Option<(AdtDef, IndexVec<Field, Ty>)> {
        if let TyKind::Indexed(BaseTy::Adt(adt_def, substs), indices) = self.kind() {
            Some((adt_def.clone(), adt_def.unfold(substs, indices, variant_idx)?))
        } else {
            panic!("type cannot be unfolded: `{self:?}`")
        }
    }
}

impl From<Expr> for Index {
    fn from(expr: Expr) -> Index {
        Index { expr, is_binder: false }
    }
}

impl From<Index> for Expr {
    fn from(index: Index) -> Expr {
        index.expr
    }
}

impl BaseTy {
    pub fn adt(adt_def: AdtDef, substs: impl IntoIterator<Item = Ty>) -> BaseTy {
        BaseTy::Adt(adt_def, Substs::new(substs.into_iter().collect_vec()))
    }
}

impl Substs {
    pub fn new<T>(tys: T) -> Substs
    where
        List<Ty>: From<T>,
    {
        Substs(Interned::from(tys))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> std::slice::Iter<Ty> {
        self.0.iter()
    }

    pub fn as_slice(&self) -> &[Ty] {
        &self.0
    }
}

impl<'a> IntoIterator for &'a Substs {
    type Item = &'a Ty;

    type IntoIter = std::slice::Iter<'a, Ty>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl Sort {
    pub fn int() -> Self {
        Interned::new(SortS { kind: SortKind::Int })
    }

    pub fn bool() -> Self {
        Interned::new(SortS { kind: SortKind::Bool })
    }

    pub fn loc() -> Self {
        Interned::new(SortS { kind: SortKind::Loc })
    }

    pub fn tuple(sorts: impl IntoIterator<Item = Sort>) -> Self {
        let sorts = sorts.into_iter().collect_vec();
        Interned::new(SortS { kind: SortKind::Tuple(sorts.into_iter().collect()) })
    }

    pub fn unit() -> Self {
        Interned::new(SortS { kind: SortKind::Tuple(vec![]) })
    }
}

impl SortS {
    pub fn kind(&self) -> &SortKind {
        &self.kind
    }

    pub fn is_loc(&self) -> bool {
        matches!(self.kind, SortKind::Loc)
    }
}

impl ExprKind {
    fn intern(self) -> Expr {
        Interned::new(ExprS { kind: self })
    }
}

impl Expr {
    pub fn tt() -> Expr {
        static TRUE: SyncOnceCell<Expr> = SyncOnceCell::new();
        TRUE.get_or_init(|| ExprKind::Constant(Constant::Bool(true)).intern())
            .clone()
    }

    pub fn zero() -> Expr {
        static ZERO: SyncOnceCell<Expr> = SyncOnceCell::new();
        ZERO.get_or_init(|| ExprKind::Constant(Constant::ZERO).intern())
            .clone()
    }

    pub fn unit() -> Expr {
        Expr::tuple(vec![])
    }

    pub fn fvar(name: Name) -> Expr {
        ExprKind::FreeVar(name).intern()
    }

    pub fn bvar(idx: u32) -> Expr {
        ExprKind::BoundVar(idx).intern()
    }

    pub fn local(local: Local) -> Expr {
        ExprKind::Local(local).intern()
    }

    pub fn constant(c: Constant) -> Expr {
        ExprKind::Constant(c).intern()
    }

    pub fn tuple(exprs: impl Into<List<Expr>>) -> Expr {
        ExprKind::Tuple(exprs.into()).intern()
    }

    pub fn from_bits(bty: &BaseTy, bits: u128) -> Expr {
        // FIXME: We are assuming the higher bits are not set. check this assumption
        match bty {
            BaseTy::Int(_) => {
                let bits = bits as i128;
                ExprKind::Constant(Constant::from(bits)).intern()
            }
            BaseTy::Uint(_) => {
                let bits = bits as u128;
                ExprKind::Constant(Constant::from(bits)).intern()
            }
            BaseTy::Bool => ExprKind::Constant(Constant::Bool(bits != 0)).intern(),
            BaseTy::Adt(_, _) => panic!(),
        }
    }

    pub fn binary_op(op: BinOp, e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(op, e1.into(), e2.into()).intern()
    }

    pub fn unary_op(op: UnOp, e: impl Into<Expr>) -> Expr {
        ExprKind::UnaryOp(op, e.into()).intern()
    }

    pub fn proj(e: impl Into<Expr>, proj: u32) -> Expr {
        ExprKind::TupleProj(e.into(), proj).intern()
    }

    pub fn path_proj(base: Expr, field: Field) -> Expr {
        ExprKind::PathProj(base, field).intern()
    }

    pub fn not(&self) -> Expr {
        ExprKind::UnaryOp(UnOp::Not, self.clone()).intern()
    }

    pub fn neg(&self) -> Expr {
        ExprKind::UnaryOp(UnOp::Neg, self.clone()).intern()
    }
}

impl ExprS {
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }

    pub fn is_true(&self) -> bool {
        matches!(self.kind, ExprKind::Constant(Constant::Bool(true)))
    }

    pub fn is_atom(&self) -> bool {
        matches!(
            self.kind,
            ExprKind::FreeVar(_)
                | ExprKind::BoundVar(_)
                | ExprKind::Constant(_)
                | ExprKind::UnaryOp(..)
                | ExprKind::Tuple(..)
                | ExprKind::PathProj(..)
        )
    }

    /// Simplify expression applying some rules like removing double negation. This is only used
    /// for pretty printing.
    pub fn simplify(&self) -> Expr {
        match self.kind() {
            ExprKind::FreeVar(name) => Expr::fvar(*name),
            ExprKind::BoundVar(idx) => Expr::bvar(*idx),
            ExprKind::Local(local) => Expr::local(*local),
            ExprKind::Constant(c) => Expr::constant(*c),
            ExprKind::BinaryOp(op, e1, e2) => Expr::binary_op(*op, e1.simplify(), e2.simplify()),
            ExprKind::UnaryOp(UnOp::Not, e) => {
                match e.kind() {
                    ExprKind::UnaryOp(UnOp::Not, e) => e.simplify(),
                    ExprKind::BinaryOp(BinOp::Eq, e1, e2) => {
                        Expr::binary_op(BinOp::Ne, e1.simplify(), e2.simplify())
                    }
                    _ => Expr::unary_op(UnOp::Not, e.simplify()),
                }
            }
            ExprKind::UnaryOp(op, e) => Expr::unary_op(*op, e.simplify()),
            ExprKind::TupleProj(e, field) => Expr::proj(e.simplify(), *field),
            ExprKind::Tuple(exprs) => Expr::tuple(exprs.iter().map(|e| e.simplify()).collect_vec()),
            ExprKind::PathProj(e, field) => Expr::path_proj(e.clone(), *field),
        }
    }

    pub fn to_loc(&self) -> Option<Loc> {
        match self.kind() {
            ExprKind::FreeVar(name) => Some(Loc::Free(*name)),
            ExprKind::Local(local) => Some(Loc::Local(*local)),
            _ => None,
        }
    }

    pub fn to_path(&self) -> Option<Path> {
        let mut expr = self;
        let mut proj = vec![];
        let loc = loop {
            match expr.kind() {
                ExprKind::PathProj(e, field) => {
                    proj.push(*field);
                    expr = e;
                }
                ExprKind::FreeVar(name) => break Loc::Free(*name),
                ExprKind::Local(local) => break Loc::Local(*local),
                _ => return None,
            }
        };
        let proj = proj.into_iter().rev().collect_vec();
        Some(Path::new(loc, proj))
    }
}

impl Pred {
    pub fn kvars<T>(kvars: T) -> Pred
    where
        List<KVar>: From<T>,
    {
        Pred::Kvars(Interned::from(kvars))
    }

    pub fn tt() -> Pred {
        Pred::Expr(Expr::tt())
    }

    pub fn is_true(&self) -> bool {
        matches!(self, Pred::Expr(e) if e.is_true())
    }

    pub fn is_atom(&self) -> bool {
        matches!(self, Pred::Kvars(..)) || matches!(self, Pred::Expr(e) if e.is_atom())
    }
}

impl KVar {
    pub fn new<T>(kvid: KVid, args: T) -> Self
    where
        List<Expr>: From<T>,
    {
        KVar(kvid, Interned::from(args))
    }

    pub fn dummy() -> KVar {
        KVar::new(KVid::from(0usize), vec![])
    }
}

impl Path {
    pub fn new<T>(loc: Loc, projection: T) -> Path
    where
        List<Field>: From<T>,
    {
        Path { loc, projection: Interned::from(projection) }
    }

    pub fn projection(&self) -> &[Field] {
        &self.projection[..]
    }

    pub fn to_expr(&self) -> Expr {
        self.projection
            .iter()
            .rev()
            .fold(self.loc.to_expr(), |e, f| Expr::path_proj(e, *f))
    }
}

impl Loc {
    pub fn to_expr(&self) -> Expr {
        match self {
            Loc::Local(local) => Expr::local(*local),
            Loc::Free(name) => Expr::fvar(*name),
        }
    }
}

impl From<Loc> for Expr {
    fn from(loc: Loc) -> Self {
        loc.to_expr()
    }
}

impl From<Expr> for Pred {
    fn from(expr: Expr) -> Self {
        Pred::Expr(expr)
    }
}

impl From<Loc> for Path {
    fn from(loc: Loc) -> Self {
        Path::new(loc, vec![])
    }
}

impl From<Name> for Loc {
    fn from(name: Name) -> Self {
        Loc::Free(name)
    }
}

impl From<Local> for Loc {
    fn from(local: Local) -> Self {
        Loc::Local(local)
    }
}

impl_internable!(
    AdtDefData,
    TyS,
    ExprS,
    SortS,
    [Ty],
    [Pred],
    [Expr],
    [Field],
    [KVar],
    [Constr],
    [Param],
    [Index]
);

mod pretty {
    use liquid_rust_common::format::PadAdapter;
    use rustc_middle::ty::TyCtxt;
    use std::fmt::Write;

    use super::*;
    use crate::pretty::*;

    impl Pretty for Binders<FnSig> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let fn_sig = &self.value;
            if f.alternate() {
                let mut padded = PadAdapter::wrap_fmt(f, 4);
                define_scoped!(cx, padded);
                w!("(\nfn")?;
                if !self.params.is_empty() {
                    w!("<{}>",
                        ^self.params.iter().format_with(", ", |param, f| {
                            f(&format_args_cx!("{:?}: {:?}", ^param.name, ^param.sort))
                        })
                    )?;
                }
                w!("({:?}) -> {:?}", join!(", ", &fn_sig.args), &fn_sig.ret)?;
                if !fn_sig.requires.is_empty() {
                    w!("\nrequires {:?} ", join!(", ", &fn_sig.requires))?;
                }
                if !fn_sig.ensures.is_empty() {
                    w!("\nensures {:?}", join!(", ", &fn_sig.ensures))?;
                }
                write!(f, "\n)")?;
            } else {
                define_scoped!(cx, f);
                if !self.params.is_empty() {
                    w!("for<{}> ",
                        ^self.params.iter().format_with(", ", |param, f| {
                            f(&format_args_cx!("{:?}: {:?}", ^param.name, ^param.sort))
                        })
                    )?;
                }
                if !fn_sig.requires.is_empty() {
                    w!("[{:?}] ", join!(", ", &fn_sig.requires))?;
                }
                w!("fn({:?}) -> {:?}", join!(", ", &fn_sig.args), &fn_sig.ret)?;
                if !fn_sig.ensures.is_empty() {
                    w!("; [{:?}]", join!(", ", &fn_sig.ensures))?;
                }
            }

            Ok(())
        }
    }

    impl Pretty for Constr {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Constr::Type(loc, ty) => w!("{:?}: {:?}", ^loc, ty),
                Constr::Pred(e) => w!("{:?}", e),
            }
        }
    }

    impl Pretty for TyS {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self.kind() {
                TyKind::Indexed(bty, indices) => fmt_bty(bty, Some(indices), cx, f),
                TyKind::Exists(bty, p) => {
                    if p.is_true() {
                        w!("{:?}", bty)
                    } else {
                        w!("{:?}{{{:?}}}", bty, p)
                    }
                }
                TyKind::Float(float_ty) => w!("{}", ^float_ty.name_str()),
                TyKind::Uninit => w!("uninit"),
                TyKind::Ptr(loc) => w!("ptr({:?})", loc),
                TyKind::Ref(RefKind::Mut, ty) => w!("&mut {:?}", ty),
                TyKind::Ref(RefKind::Shr, ty) => w!("&{:?}", ty),
                TyKind::Param(param) => w!("{}", ^param),
                TyKind::Tuple(tys) => w!("({:?})", join!(", ", tys)),
                TyKind::Never => w!("!"),
                TyKind::Discr => w!("discr"),
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for BaseTy {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt_bty(self, None, cx, f)
        }
    }

    fn fmt_bty(
        bty: &BaseTy,
        indices: Option<&[Index]>,
        cx: &PPrintCx,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        define_scoped!(cx, f);
        match bty {
            BaseTy::Int(int_ty) => write!(f, "{}", int_ty.name_str())?,
            BaseTy::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str())?,
            BaseTy::Bool => w!("bool")?,
            BaseTy::Adt(adt_def, _) => w!("{:?}", adt_def.def_id())?,
        }
        match bty {
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => {
                if let Some(idx) = indices {
                    w!("<{:?}>", join!(", ", idx))?;
                }
            }
            BaseTy::Adt(_, args) => {
                if !args.is_empty() || indices.is_some() {
                    w!("<")?;
                }
                w!("{:?}", join!(", ", args))?;
                if let Some(exprs) = indices {
                    if !args.is_empty() {
                        w!(", ")?;
                    }
                    w!("{:?}", join!(", ", exprs))?;
                }
                if !args.is_empty() || indices.is_some() {
                    w!(">")?;
                }
            }
        }
        Ok(())
    }

    impl Pretty for Index {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            if self.is_binder && self.expr.is_atom() {
                w!("@{:?}", &self.expr)
            } else if self.is_binder {
                w!("@({:?})", &self.expr)
            } else {
                w!("{:?}", &self.expr)
            }
        }
    }

    impl Pretty for Pred {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Pred::Kvars(kvars) => {
                    if let [kvar] = &kvars[..] {
                        w!("{:?}", kvar)
                    } else {
                        w!("({:?})", join!(" ∧ ", kvars))
                    }
                }
                Pred::Expr(expr) => w!("{:?}", expr),
                Pred::Hole => w!("*"),
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).fully_qualified_paths(true)
        }
    }

    impl Pretty for KVar {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let KVar(kvid, args) = self;

            w!("{:?}", ^kvid)?;
            match cx.kvar_args {
                Visibility::Show => w!("({:?})", join!(", ", args))?,
                Visibility::Truncate(n) => w!("({:?})", join!(", ", args.iter().take(n)))?,
                Visibility::Hide => {}
            }
            Ok(())
        }
    }

    impl Pretty for ExprS {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            fn should_parenthesize(op: BinOp, child: &ExprS) -> bool {
                if let ExprKind::BinaryOp(child_op, ..) = child.kind() {
                    child_op.precedence() < op.precedence()
                        || (child_op.precedence() == op.precedence()
                            && !op.precedence().is_associative())
                } else {
                    false
                }
            }
            let e = if cx.simplify_exprs { self.simplify() } else { Interned::new(self.clone()) };
            match e.kind() {
                ExprKind::FreeVar(name) => w!("{:?}", ^name),
                ExprKind::BoundVar(idx) => w!("ν{}", ^idx),
                ExprKind::Local(local) => w!("{:?}", ^local),
                ExprKind::BinaryOp(op, e1, e2) => {
                    if should_parenthesize(*op, e1) {
                        w!("({:?})", e1)?;
                    } else {
                        w!("{:?}", e1)?;
                    }
                    if matches!(op, BinOp::Div) {
                        w!("{:?}", op)?;
                    } else {
                        w!(" {:?} ", op)?;
                    }
                    if should_parenthesize(*op, e2) {
                        w!("({:?})", e2)?;
                    } else {
                        w!("{:?}", e2)?;
                    }
                    Ok(())
                }
                ExprKind::Constant(c) => w!("{}", ^c),
                ExprKind::UnaryOp(op, e) => {
                    if e.is_atom() {
                        w!("{:?}{:?}", op, e)
                    } else {
                        w!("{:?}({:?})", op, e)
                    }
                }
                ExprKind::TupleProj(e, field) => {
                    if e.is_atom() {
                        w!("{:?}.{:?}", e, ^field)
                    } else {
                        w!("({:?}).{:?}", e, ^field)
                    }
                }
                ExprKind::Tuple(exprs) => {
                    w!("({:?})", join!(", ", exprs))
                }
                ExprKind::PathProj(e, field) => {
                    if e.is_atom() {
                        w!("{:?}.{:?}", e, field)
                    } else {
                        w!("({:?}).{:?}", e, field)
                    }
                }
            }
        }
    }

    impl Pretty for Path {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", self.loc)?;
            for field in self.projection.iter() {
                w!(".{}", ^u32::from(*field))?;
            }
            Ok(())
        }
    }

    impl Pretty for Loc {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Loc::Local(local) => w!("{:?}", ^local),
                Loc::Free(name) => w!("{:?}", ^name),
            }
        }
    }

    impl Pretty for Sort {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self.kind() {
                SortKind::Int => w!("int"),
                SortKind::Bool => w!("bool"),
                SortKind::Loc => w!("loc"),
                SortKind::Tuple(sorts) => w!("({:?})", join!(", ", sorts)),
            }
        }
    }

    impl Pretty for BinOp {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                BinOp::Iff => w!("⇔"),
                BinOp::Imp => w!("⇒"),
                BinOp::Or => w!("∨"),
                BinOp::And => w!("∧"),
                BinOp::Eq => w!("="),
                BinOp::Ne => w!("≠"),
                BinOp::Gt => w!(">"),
                BinOp::Ge => w!("≥"),
                BinOp::Lt => w!("<"),
                BinOp::Le => w!("≤"),
                BinOp::Add => w!("+"),
                BinOp::Sub => w!("-"),
                BinOp::Mul => w!("*"),
                BinOp::Div => w!("/"),
                BinOp::Mod => w!("mod"),
            }
        }
    }

    impl Pretty for UnOp {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                UnOp::Not => w!("¬"),
                UnOp::Neg => w!("-"),
            }
        }
    }

    impl fmt::Display for Sort {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt::Debug::fmt(self, f)
        }
    }

    impl_debug_with_default_cx!(
        Constr,
        TyS => "ty",
        BaseTy,
        Pred,
        Sort,
        ExprS,
        Loc,
        Binders<FnSig>,
        Path,
        KVar,
    );
}
