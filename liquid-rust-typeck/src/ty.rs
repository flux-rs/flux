use std::{fmt, lazy::SyncOnceCell};

use itertools::Itertools;
use liquid_rust_common::index::IndexVec;
// use liquid_rust_common::index::Idx;
pub use liquid_rust_core::{ir::Field, ty::ParamTy};
use liquid_rust_core::{ir::Local, ty::Layout};
pub use liquid_rust_fixpoint::{BinOp, Constant, KVid, UnOp};
use rustc_hash::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
pub use rustc_middle::ty::{FloatTy, IntTy, UintTy};

use crate::{
    global_env::GlobalEnv,
    intern::{impl_internable, Interned},
    pure_ctxt::Scope,
    subst::Subst,
};

pub enum AdtDef {
    Transparent { refined_by: Vec<Param>, fields: Vec<Ty> },
    Opaque { refined_by: Vec<Param> },
}

#[derive(Debug)]
pub struct FnSpec {
    pub fn_sig: Binders<FnSig>,
    pub assume: bool,
}

pub struct Binders<T> {
    pub params: Vec<Param>,
    pub value: T,
}

#[derive(Debug)]
pub struct FnSig {
    pub requires: Vec<Constr>,
    pub args: Vec<Ty>,
    pub ret: Ty,
    pub ensures: Vec<Constr>,
}

pub enum Constr {
    Type(Loc, Ty),
    Pred(Expr),
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: String,
    pub args: Vec<(Name, Sort)>,
    pub expr: Expr,
}

#[derive(Debug)]
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
    Refine(BaseTy, Expr),
    Exists(BaseTy, Pred),
    Float(FloatTy),
    Uninit(Layout),
    StrgRef(Loc),
    WeakRef(Ty),
    ShrRef(Ty),
    Param(ParamTy),
}

#[derive(Clone)]
pub struct Path {
    pub loc: Loc,
    projection: Interned<[Field]>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Loc {
    Local(Local),
    Abstract(Name),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Adt(DefId, Substs),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Substs(Interned<[Ty]>);

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Pred {
    KVar(KVid, Interned<[Expr]>),
    Expr(Expr),
}

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
    Var(Var),
    Constant(Constant),
    BinaryOp(BinOp, Expr, Expr),
    UnaryOp(UnOp, Expr),
    Proj(Expr, u32),
    Tuple(Vec<Expr>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Var {
    Bound,
    Free(Name),
}

newtype_index! {
    pub struct Name {
        DEBUG_FORMAT = "a{}",
    }
}

impl<T> Binders<T> {
    pub fn new(params: Vec<Param>, value: T) -> Binders<T> {
        Binders { params, value }
    }
}

impl AdtDef {
    pub fn refined_by(&self) -> &[Param] {
        match self {
            AdtDef::Transparent { refined_by, .. } | AdtDef::Opaque { refined_by, .. } => {
                refined_by
            }
        }
    }

    pub fn sort(&self) -> Sort {
        Sort::tuple(self.refined_by().iter().map(|param| param.sort.clone()))
    }

    pub fn unfold(&self, substs: &Substs, e: &Expr) -> IndexVec<Field, Ty> {
        let mut subst = Subst::with_type_substs(substs.as_slice());
        match (e.kind(), self.refined_by()) {
            (ExprKind::Tuple(exprs), refined_by) => {
                debug_assert_eq!(exprs.len(), self.refined_by().len());
                for (e, param) in exprs.iter().zip(refined_by) {
                    subst.insert_expr_subst(param.name, e.clone());
                }
            }
            (_, [param]) => {
                subst.insert_expr_subst(param.name, e.clone());
            }
            _ => panic!("invalid sort for expr: `{e:?}`"),
        }
        match self {
            AdtDef::Transparent { fields, .. } => {
                fields.iter().map(|ty| subst.subst_ty(ty)).collect()
            }
            AdtDef::Opaque { .. } => panic!("unfolding opaque adt"),
        }
    }

    pub fn unfold_uninit(&self) -> IndexVec<Field, Ty> {
        match self {
            AdtDef::Transparent { fields, .. } => {
                fields.iter().map(|ty| Ty::uninit(ty.layout())).collect()
            }
            AdtDef::Opaque { .. } => panic!("unfolding opaque adt"),
        }
    }

    pub fn fold(&self, tys: &[Ty]) -> Expr {
        match self {
            AdtDef::Transparent { fields, refined_by } => {
                debug_assert_eq!(fields.len(), tys.len());
                let mut subst = Subst::empty();
                let params = refined_by.iter().map(|param| param.name).collect();
                for (ty, field) in tys.iter().zip(fields) {
                    subst.infer_from_tys(&params, ty, field);
                }
                Expr::tuple(refined_by.iter().map(|param| subst.get_expr(param.name)))
            }
            AdtDef::Opaque { .. } => panic!("folding opaque adt"),
        }
    }
}

impl Ty {
    pub fn strg_ref(loc: impl Into<Loc>) -> Ty {
        TyKind::StrgRef(loc.into()).intern()
    }

    pub fn weak_ref(ty: Ty) -> Ty {
        TyKind::WeakRef(ty).intern()
    }

    pub fn shr_ref(ty: Ty) -> Ty {
        TyKind::ShrRef(ty).intern()
    }

    pub fn uninit(layout: Layout) -> Ty {
        TyKind::Uninit(layout).intern()
    }

    pub fn refine(bty: BaseTy, e: impl Into<Expr>) -> Ty {
        TyKind::Refine(bty, e.into()).intern()
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
        matches!(self.kind(), TyKind::Uninit(..))
    }

    pub fn walk(&self, f: &mut impl FnMut(&TyS)) {
        f(self);
        match self.kind() {
            TyKind::WeakRef(ty) => ty.walk(f),
            TyKind::Refine(bty, _) | TyKind::Exists(bty, _) => bty.walk(f),
            _ => {}
        }
    }

    pub fn layout(&self) -> Layout {
        match self.kind() {
            TyKind::Refine(bty, _) | TyKind::Exists(bty, _) => bty.layout(),
            TyKind::Float(float_ty) => Layout::Float(*float_ty),
            TyKind::Uninit(layout) => *layout,
            TyKind::StrgRef(_) | TyKind::WeakRef(_) | TyKind::ShrRef(_) => Layout::Ref,
            TyKind::Param(_) => Layout::Param,
        }
    }

    pub fn deref(&self, derefs: u32) -> Ty {
        let mut ty = self;
        for _ in 0..derefs {
            match self.kind() {
                TyKind::ShrRef(ref_ty) => ty = &*ref_ty,
                _ => panic!("dereferencing non-reference type: `{:?}`", self),
            }
        }
        Interned::new(ty.clone())
    }

    pub fn unfold(&self, genv: &GlobalEnv) -> (DefId, IndexVec<Field, Ty>) {
        match self.kind() {
            TyKind::Refine(BaseTy::Adt(did, substs), e) => {
                let adt_def = genv.adt_def(*did);
                (*did, adt_def.unfold(substs, e))
            }
            TyKind::Uninit(Layout::Adt(did)) => {
                let adt_def = genv.adt_def(*did);
                (*did, adt_def.unfold_uninit())
            }
            _ => panic!("type cannot be unfolded: `{self:?}`"),
        }
    }
}

impl BaseTy {
    pub fn adt(def_id: DefId, substs: impl IntoIterator<Item = Ty>) -> BaseTy {
        BaseTy::Adt(def_id, Substs::new(&substs.into_iter().collect_vec()))
    }

    fn walk(&self, f: &mut impl FnMut(&TyS)) {
        if let BaseTy::Adt(_, substs) = self {
            substs.iter().for_each(|ty| ty.walk(f));
        }
    }

    fn layout(&self) -> Layout {
        match self {
            BaseTy::Int(int_ty) => Layout::Int(*int_ty),
            BaseTy::Uint(uint_ty) => Layout::Uint(*uint_ty),
            BaseTy::Bool => Layout::Bool,
            BaseTy::Adt(did, _) => Layout::Adt(*did),
        }
    }
}

impl Substs {
    pub fn new(tys: &[Ty]) -> Substs {
        Substs(Interned::new_slice(tys))
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
        let mut sorts = sorts.into_iter().collect_vec();
        if sorts.len() == 1 {
            sorts.remove(0)
        } else {
            Interned::new(SortS { kind: SortKind::Tuple(sorts.into_iter().collect()) })
        }
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
        Expr::tuple([])
    }

    pub fn var(var: impl Into<Var>) -> Expr {
        ExprKind::Var(var.into()).intern()
    }

    pub fn constant(c: Constant) -> Expr {
        ExprKind::Constant(c).intern()
    }

    pub fn tuple(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        let mut exprs = exprs.into_iter().collect_vec();
        if exprs.len() == 1 {
            exprs.remove(0)
        } else {
            ExprKind::Tuple(exprs).intern()
        }
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
        ExprKind::Proj(e.into(), proj).intern()
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
            ExprKind::Var(_) | ExprKind::Constant(_) | ExprKind::UnaryOp(..) | ExprKind::Tuple(..)
        )
    }

    pub fn subst_bound_vars(&self, to: impl Into<Expr>) -> Expr {
        let to = to.into();
        match self.kind() {
            ExprKind::Var(var) => {
                match var {
                    Var::Bound => to,
                    Var::Free(_) => ExprKind::Var(*var).intern(),
                }
            }
            ExprKind::Constant(c) => ExprKind::Constant(*c).intern(),
            ExprKind::BinaryOp(op, e1, e2) => {
                ExprKind::BinaryOp(*op, e1.subst_bound_vars(to.clone()), e2.subst_bound_vars(to))
                    .intern()
            }
            ExprKind::UnaryOp(op, e) => ExprKind::UnaryOp(*op, e.subst_bound_vars(to)).intern(),
            ExprKind::Proj(e, field) => ExprKind::Proj(e.subst_bound_vars(to), *field).intern(),
            ExprKind::Tuple(exprs) => {
                Expr::tuple(exprs.iter().map(|e| e.subst_bound_vars(to.clone())))
            }
        }
    }

    pub fn vars(&self) -> FxHashSet<Name> {
        fn go(e: &ExprS, vars: &mut FxHashSet<Name>) {
            match e.kind() {
                ExprKind::Var(Var::Free(name)) => {
                    vars.insert(*name);
                }
                ExprKind::BinaryOp(_, e1, e2) => {
                    go(e1, vars);
                    go(e2, vars);
                }
                ExprKind::UnaryOp(_, e) => go(e, vars),
                ExprKind::Proj(e, _) => go(e, vars),
                ExprKind::Tuple(exprs) => exprs.iter().for_each(|e| go(e, vars)),
                ExprKind::Var(Var::Bound) | ExprKind::Constant(_) => {}
            }
        }
        let mut vars = FxHashSet::default();
        go(self, &mut vars);
        vars
    }

    pub fn has_free_vars(&self, scope: &Scope) -> bool {
        self.vars().into_iter().any(|name| !scope.contains(name))
    }

    /// Simplify expression applying some rules like removing double negation. This is used for pretty
    /// printing.
    pub fn simplify(&self) -> Expr {
        match self.kind() {
            ExprKind::Var(var) => ExprKind::Var(*var).intern(),
            ExprKind::Constant(c) => ExprKind::Constant(*c).intern(),
            ExprKind::BinaryOp(op, e1, e2) => {
                ExprKind::BinaryOp(*op, e1.simplify(), e2.simplify()).intern()
            }
            ExprKind::UnaryOp(UnOp::Not, e) => {
                match e.kind() {
                    ExprKind::UnaryOp(UnOp::Not, e) => e.simplify(),
                    ExprKind::BinaryOp(BinOp::Eq, e1, e2) => {
                        ExprKind::BinaryOp(BinOp::Ne, e1.simplify(), e2.simplify()).intern()
                    }
                    _ => ExprKind::UnaryOp(UnOp::Not, e.simplify()).intern(),
                }
            }
            ExprKind::UnaryOp(op, e) => ExprKind::UnaryOp(*op, e.simplify()).intern(),
            ExprKind::Proj(e, field) => ExprKind::Proj(e.simplify(), *field).intern(),
            ExprKind::Tuple(exprs) => Expr::tuple(exprs.iter().map(|e| e.simplify())),
        }
    }
}

impl From<Expr> for Pred {
    fn from(expr: Expr) -> Self {
        Pred::Expr(expr)
    }
}

impl Pred {
    pub fn kvar(kvid: KVid, args: impl IntoIterator<Item = Expr>) -> Self {
        Pred::KVar(kvid, Interned::new_slice(&args.into_iter().collect_vec()))
    }

    pub fn dummy_kvar() -> Pred {
        Pred::kvar(KVid::from(0u32), [])
    }

    pub fn is_atom(&self) -> bool {
        matches!(self, Pred::KVar(_, _)) || matches!(self, Pred::Expr(e) if e.is_atom())
    }

    pub fn subst_bound_vars(&self, to: impl Into<Expr>) -> Self {
        let to = to.into();
        match self {
            Pred::KVar(kvid, args) => {
                Pred::kvar(*kvid, args.iter().map(|arg| arg.subst_bound_vars(to.clone())))
            }
            Pred::Expr(e) => Pred::Expr(e.subst_bound_vars(to)),
        }
    }

    pub fn tt() -> Pred {
        Pred::Expr(Expr::tt())
    }

    pub fn is_true(&self) -> bool {
        match self {
            Pred::KVar(..) => false,
            Pred::Expr(e) => e.is_true(),
        }
    }
}

impl From<Var> for Expr {
    fn from(var: Var) -> Self {
        ExprKind::Var(var).intern()
    }
}

impl Path {
    pub fn new(loc: Loc, projection: &[Field]) -> Path {
        Path { loc, projection: Interned::new_slice(projection) }
    }

    pub fn projection(&self) -> &[Field] {
        &self.projection[..]
    }
}

impl Loc {
    pub fn is_free(&self, scope: &Scope) -> bool {
        match self {
            Loc::Local(_) => false,
            Loc::Abstract(name) => !scope.contains(*name),
        }
    }
}

impl From<Name> for Loc {
    fn from(name: Name) -> Self {
        Loc::Abstract(name)
    }
}

impl From<Local> for Loc {
    fn from(local: Local) -> Self {
        Loc::Local(local)
    }
}

impl PartialOrd for Loc {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Loc::Local(local1), Loc::Local(local2)) => local1.partial_cmp(local2),
            (Loc::Local(_), Loc::Abstract(_)) => Some(std::cmp::Ordering::Less),
            (Loc::Abstract(_), Loc::Local(_)) => Some(std::cmp::Ordering::Greater),
            (Loc::Abstract(loc1), Loc::Abstract(loc2)) => loc1.partial_cmp(loc2),
        }
    }
}

impl Ord for Loc {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl From<Name> for Var {
    fn from(v: Name) -> Self {
        Self::Free(v)
    }
}

impl<'a> From<&'a Name> for Var {
    fn from(v: &'a Name) -> Self {
        Self::Free(*v)
    }
}

impl_internable!(TyS, ExprS, [Expr], [Ty], [Field], SortS);

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
                TyKind::Refine(bty, e) => fmt_bty(bty, Some(e), cx, f),
                TyKind::Exists(bty, p) => {
                    if p.is_true() {
                        w!("{:?}", bty)
                    } else {
                        w!("{:?}{{{:?}}}", bty, p)
                    }
                }
                TyKind::Float(float_ty) => w!("{}", ^float_ty.name_str()),
                TyKind::Uninit(_) => w!("uninit"),
                TyKind::StrgRef(loc) => w!("ref<{:?}>", loc),
                TyKind::WeakRef(ty) => w!("&weak {:?}", ty),
                TyKind::ShrRef(ty) => w!("&{:?}", ty),
                TyKind::Param(param) => w!("{}", ^param),
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
        e: Option<&ExprS>,
        cx: &PPrintCx,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        define_scoped!(cx, f);
        match bty {
            BaseTy::Int(int_ty) => write!(f, "{}", int_ty.name_str())?,
            BaseTy::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str())?,
            BaseTy::Bool => w!("bool")?,
            BaseTy::Adt(did, _) => w!("{:?}", did)?,
        }
        match bty {
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => {
                if let Some(e) = e {
                    w!("<{:?}>", e)?;
                }
            }
            BaseTy::Adt(_, args) => {
                if !args.is_empty() || e.is_some() {
                    w!("<")?;
                }
                w!("{:?}", join!(", ", args))?;
                if let Some(e) = e {
                    if !args.is_empty() {
                        w!(", ")?;
                    }
                    w!("{:?}", e)?;
                }
                if !args.is_empty() || e.is_some() {
                    w!(">")?;
                }
            }
        }
        Ok(())
    }

    impl Pretty for Pred {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Self::KVar(kvid, args) => {
                    w!("{:?}", ^kvid)?;
                    match cx.kvar_args {
                        Visibility::Show => w!("({:?})", join!(", ", args))?,
                        Visibility::Truncate(n) => w!("({:?})", join!(", ", args.iter().take(n)))?,
                        Visibility::Hide => {}
                    }
                    Ok(())
                }
                Self::Expr(expr) => w!("{:?}", expr),
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).fully_qualified_paths(true)
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
                ExprKind::Var(x) => w!("{:?}", ^x),
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
                ExprKind::Proj(e, field) => {
                    if e.is_atom() {
                        w!("{:?}.{:?}", e, ^field)
                    } else {
                        w!("({:?}).{:?}", e, ^field)
                    }
                }
                ExprKind::Tuple(exprs) => {
                    w!("({:?})", join!(", ", exprs))
                }
            }
        }
    }

    impl Pretty for Var {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Var::Bound => w!("ν"),
                Var::Free(var) => w!("{:?}", ^var),
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
                Loc::Abstract(name) => w!("{:?}", ^name),
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
        TyS,
        BaseTy,
        Pred,
        Sort,
        ExprS,
        Var,
        Loc,
        Binders<FnSig>,
        Path
    );
}
