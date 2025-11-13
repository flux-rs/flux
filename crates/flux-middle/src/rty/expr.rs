use std::{fmt, iter, ops::ControlFlow, sync::OnceLock};

use flux_arc_interner::{Interned, List, impl_internable, impl_slice_internable};
use flux_common::bug;
use flux_macros::{TypeFoldable, TypeVisitable};
use flux_rustc_bridge::{
    ToRustc,
    const_eval::{scalar_to_bits, scalar_to_int, scalar_to_uint},
    ty::{Const, ConstKind, ValTree, VariantIdx},
};
use itertools::Itertools;
use liquid_fixpoint::ThyFunc;
use rustc_abi::{FIRST_VARIANT, FieldIdx};
use rustc_data_structures::snapshot_map::SnapshotMap;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::{
    mir::Local,
    ty::{ParamConst, ScalarInt, TyCtxt},
};
use rustc_span::{Span, Symbol};
use rustc_type_ir::{BoundVar, DebruijnIndex, INNERMOST};

use super::{
    BaseTy, Binder, BoundReftKind, BoundVariableKinds, FuncSort, GenericArgs, GenericArgsExt as _,
    IntTy, Sort, UintTy,
};
use crate::{
    big_int::BigInt,
    def_id::FluxDefId,
    fhir::{self},
    global_env::GlobalEnv,
    pretty::*,
    queries::QueryResult,
    rty::{
        BoundVariableKind, SortArg,
        fold::{
            TypeFoldable, TypeFolder, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable as _,
            TypeVisitor,
        },
    },
};

/// A lambda abstraction with an elaborated output sort. We need the output sort of lambdas for
/// encoding into fixpoint
#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable)]
pub struct Lambda {
    body: Binder<Expr>,
    output: Sort,
}

impl Lambda {
    pub fn bind_with_vars(body: Expr, inputs: BoundVariableKinds, output: Sort) -> Self {
        debug_assert!(inputs.iter().all(BoundVariableKind::is_refine));
        Self { body: Binder::bind_with_vars(body, inputs), output }
    }

    pub fn bind_with_fsort(body: Expr, fsort: FuncSort) -> Self {
        Self { body: Binder::bind_with_sorts(body, fsort.inputs()), output: fsort.output().clone() }
    }

    pub fn apply(&self, args: &[Expr]) -> Expr {
        self.body.replace_bound_refts(args)
    }

    pub fn vars(&self) -> &BoundVariableKinds {
        self.body.vars()
    }

    pub fn output(&self) -> Sort {
        self.output.clone()
    }

    pub fn fsort(&self) -> FuncSort {
        let inputs_and_output = self
            .vars()
            .iter()
            .map(|kind| kind.expect_sort().clone())
            .chain(iter::once(self.output()))
            .collect();
        FuncSort { inputs_and_output }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable)]
pub struct AliasReft {
    /// Id of the associated refinement in the trait
    pub assoc_id: FluxDefId,
    pub args: GenericArgs,
}

impl AliasReft {
    pub fn to_rustc_trait_ref<'tcx>(&self, tcx: TyCtxt<'tcx>) -> rustc_middle::ty::TraitRef<'tcx> {
        let trait_def_id = self.assoc_id.parent();
        let args = self
            .args
            .to_rustc(tcx)
            .truncate_to(tcx, tcx.generics_of(trait_def_id));
        rustc_middle::ty::TraitRef::new(tcx, trait_def_id, args)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct Expr {
    kind: Interned<ExprKind>,
    espan: Option<ESpan>,
}

impl Expr {
    pub fn at_opt(self, espan: Option<ESpan>) -> Expr {
        Expr { kind: self.kind, espan }
    }

    pub fn at(self, espan: ESpan) -> Expr {
        self.at_opt(Some(espan))
    }

    pub fn at_base(self, base: ESpan) -> Expr {
        if let Some(espan) = self.espan { self.at(espan.with_base(base)) } else { self }
    }

    pub fn span(&self) -> Option<ESpan> {
        self.espan
    }

    pub fn tt() -> Expr {
        static TRUE: OnceLock<Expr> = OnceLock::new();
        TRUE.get_or_init(|| ExprKind::Constant(Constant::Bool(true)).intern())
            .clone()
    }

    pub fn ff() -> Expr {
        static FALSE: OnceLock<Expr> = OnceLock::new();
        FALSE
            .get_or_init(|| ExprKind::Constant(Constant::Bool(false)).intern())
            .clone()
    }

    pub fn and_from_iter(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        exprs
            .into_iter()
            .reduce(|acc, e| Expr::binary_op(BinOp::And, acc, e))
            .unwrap_or_else(Expr::tt)
    }

    pub fn or_from_iter(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        exprs
            .into_iter()
            .reduce(|acc, e| Expr::binary_op(BinOp::Or, acc, e))
            .unwrap_or_else(Expr::ff)
    }

    pub fn and(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        Expr::and_from_iter([e1.into(), e2.into()])
    }

    pub fn or(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        Expr::or_from_iter([e1.into(), e2.into()])
    }

    pub fn zero() -> Expr {
        static ZERO: OnceLock<Expr> = OnceLock::new();
        ZERO.get_or_init(|| ExprKind::Constant(Constant::ZERO).intern())
            .clone()
    }

    pub fn int_max(int_ty: IntTy) -> Expr {
        let bit_width: u64 = int_ty
            .bit_width()
            .unwrap_or(flux_config::pointer_width().bits());
        Expr::constant(Constant::int_max(bit_width.try_into().unwrap()))
    }

    pub fn int_min(int_ty: IntTy) -> Expr {
        let bit_width: u64 = int_ty
            .bit_width()
            .unwrap_or(flux_config::pointer_width().bits());
        Expr::constant(Constant::int_min(bit_width.try_into().unwrap()))
    }

    pub fn uint_max(uint_ty: UintTy) -> Expr {
        let bit_width: u64 = uint_ty
            .bit_width()
            .unwrap_or(flux_config::pointer_width().bits());
        Expr::constant(Constant::uint_max(bit_width.try_into().unwrap()))
    }

    pub fn nu() -> Expr {
        Expr::bvar(INNERMOST, BoundVar::ZERO, BoundReftKind::Anon)
    }

    pub fn is_nu(&self) -> bool {
        if let ExprKind::Var(Var::Bound(INNERMOST, var)) = self.kind()
            && var.var == BoundVar::ZERO
        {
            true
        } else {
            false
        }
    }

    pub fn unit() -> Expr {
        Expr::tuple(List::empty())
    }

    pub fn var(var: Var) -> Expr {
        ExprKind::Var(var).intern()
    }

    pub fn fvar(name: Name) -> Expr {
        Var::Free(name).to_expr()
    }

    pub fn evar(evid: EVid) -> Expr {
        Var::EVar(evid).to_expr()
    }

    pub fn bvar(debruijn: DebruijnIndex, var: BoundVar, kind: BoundReftKind) -> Expr {
        Var::Bound(debruijn, BoundReft { var, kind }).to_expr()
    }

    pub fn early_param(index: u32, name: Symbol) -> Expr {
        Var::EarlyParam(EarlyReftParam { index, name }).to_expr()
    }

    pub fn local(local: Local) -> Expr {
        ExprKind::Local(local).intern()
    }

    pub fn constant(c: Constant) -> Expr {
        ExprKind::Constant(c).intern()
    }

    pub fn const_def_id(c: DefId) -> Expr {
        ExprKind::ConstDefId(c).intern()
    }

    pub fn const_generic(param: ParamConst) -> Expr {
        ExprKind::Var(Var::ConstGeneric(param)).intern()
    }

    pub fn tuple(flds: List<Expr>) -> Expr {
        ExprKind::Tuple(flds).intern()
    }

    pub fn ctor_struct(def_id: DefId, flds: List<Expr>) -> Expr {
        ExprKind::Ctor(Ctor::Struct(def_id), flds).intern()
    }

    pub fn ctor_enum(def_id: DefId, idx: VariantIdx) -> Expr {
        ExprKind::Ctor(Ctor::Enum(def_id, idx), List::empty()).intern()
    }

    pub fn ctor(ctor: Ctor, flds: List<Expr>) -> Expr {
        ExprKind::Ctor(ctor, flds).intern()
    }

    pub fn is_ctor(def_id: DefId, variant_idx: VariantIdx, idx: impl Into<Expr>) -> Expr {
        ExprKind::IsCtor(def_id, variant_idx, idx.into()).intern()
    }

    pub fn from_bits(bty: &BaseTy, bits: u128) -> Expr {
        // FIXME: We are assuming the higher bits are not set. check this assumption
        match bty {
            BaseTy::Int(_) => {
                let bits = bits as i128;
                ExprKind::Constant(Constant::from(bits)).intern()
            }
            BaseTy::Uint(_) => ExprKind::Constant(Constant::from(bits)).intern(),
            BaseTy::Bool => ExprKind::Constant(Constant::Bool(bits != 0)).intern(),
            BaseTy::Char => {
                let c = char::from_u32(bits.try_into().unwrap()).unwrap();
                ExprKind::Constant(Constant::Char(c)).intern()
            }
            _ => bug!(),
        }
    }

    pub fn ite(p: impl Into<Expr>, e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::IfThenElse(p.into(), e1.into(), e2.into()).intern()
    }

    fn empty() -> Expr {
        let func = Self::global_func(SpecFuncKind::Thy(ThyFunc::SetEmpty));
        Expr::app(func, List::empty(), List::from_arr([Expr::zero()]))
    }

    fn singleton(elem: Expr) -> Expr {
        let func = Self::global_func(SpecFuncKind::Thy(ThyFunc::SetSng));
        Expr::app(func, List::empty(), List::from_arr([elem]))
    }

    fn union(expr1: Expr, expr2: Expr) -> Expr {
        let func = Self::global_func(SpecFuncKind::Thy(ThyFunc::SetCup));
        Expr::app(func, List::empty(), List::from_arr([expr1, expr2]))
    }

    pub fn set(elems: List<Expr>) -> Expr {
        let mut expr = Expr::empty();
        for elem in &elems {
            expr = Self::union(expr, Self::singleton(elem.clone()));
        }
        expr
    }

    pub fn abs(lam: Lambda) -> Expr {
        ExprKind::Abs(lam).intern()
    }

    pub fn let_(init: Expr, body: Binder<Expr>) -> Expr {
        ExprKind::Let(init, body).intern()
    }

    pub fn bounded_quant(kind: fhir::QuantKind, rng: fhir::Range, body: Binder<Expr>) -> Expr {
        ExprKind::BoundedQuant(kind, rng, body).intern()
    }

    pub fn hole(kind: HoleKind) -> Expr {
        ExprKind::Hole(kind).intern()
    }

    pub fn kvar(kvar: KVar) -> Expr {
        ExprKind::KVar(kvar).intern()
    }

    pub fn alias(alias: AliasReft, args: List<Expr>) -> Expr {
        ExprKind::Alias(alias, args).intern()
    }

    pub fn forall(expr: Binder<Expr>) -> Expr {
        ExprKind::ForAll(expr).intern()
    }

    pub fn exists(expr: Binder<Expr>) -> Expr {
        ExprKind::Exists(expr).intern()
    }

    pub fn binary_op(op: BinOp, e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(op, e1.into(), e2.into()).intern()
    }

    pub fn prim_val(op: BinOp, e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        Expr::app(InternalFuncKind::Val(op), List::empty(), List::from_arr([e1.into(), e2.into()]))
    }

    pub fn prim_rel(op: BinOp, e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        Expr::app(InternalFuncKind::Rel(op), List::empty(), List::from_arr([e1.into(), e2.into()]))
    }

    pub fn unit_struct(def_id: DefId) -> Expr {
        Expr::ctor_struct(def_id, List::empty())
    }

    pub fn cast(from: Sort, to: Sort, idx: Expr) -> Expr {
        Expr::app(
            InternalFuncKind::Cast,
            List::from_arr([SortArg::Sort(from), SortArg::Sort(to)]),
            List::from_arr([idx]),
        )
    }

    pub fn app(func: impl Into<Expr>, sort_args: List<SortArg>, args: List<Expr>) -> Expr {
        ExprKind::App(func.into(), sort_args, args).intern()
    }

    pub fn global_func(kind: SpecFuncKind) -> Expr {
        ExprKind::GlobalFunc(kind).intern()
    }

    pub fn internal_func(kind: InternalFuncKind) -> Expr {
        ExprKind::InternalFunc(kind).intern()
    }

    pub fn eq(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Eq, e1.into(), e2.into()).intern()
    }

    pub fn unary_op(op: UnOp, e: impl Into<Expr>) -> Expr {
        ExprKind::UnaryOp(op, e.into()).intern()
    }

    pub fn ne(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Ne, e1.into(), e2.into()).intern()
    }

    pub fn ge(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Ge(Sort::Int), e1.into(), e2.into()).intern()
    }

    pub fn gt(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Gt(Sort::Int), e1.into(), e2.into()).intern()
    }

    pub fn lt(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Lt(Sort::Int), e1.into(), e2.into()).intern()
    }

    pub fn le(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Le(Sort::Int), e1.into(), e2.into()).intern()
    }

    pub fn implies(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Imp, e1.into(), e2.into()).intern()
    }

    pub fn field_proj(e: impl Into<Expr>, proj: FieldProj) -> Expr {
        ExprKind::FieldProj(e.into(), proj).intern()
    }

    pub fn field_projs(e: impl Into<Expr>, projs: &[FieldProj]) -> Expr {
        projs.iter().copied().fold(e.into(), Expr::field_proj)
    }

    pub fn path_proj(base: Expr, field: FieldIdx) -> Expr {
        ExprKind::PathProj(base, field).intern()
    }

    pub fn not(&self) -> Expr {
        ExprKind::UnaryOp(UnOp::Not, self.clone()).intern()
    }

    pub fn neg(&self) -> Expr {
        ExprKind::UnaryOp(UnOp::Neg, self.clone()).intern()
    }

    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }

    /// An expression is an *atom* if it is "self-delimiting", i.e., it has a clear boundary
    /// when printed. This is used to avoid unnecessary parenthesis when pretty printing.
    pub fn is_atom(&self) -> bool {
        !matches!(self.kind(), ExprKind::Abs(..) | ExprKind::BinaryOp(..) | ExprKind::ForAll(..))
    }

    /// Simple syntactic check to see if the expression is a trivially true predicate. This is used
    /// mostly for filtering predicates when pretty printing but also to simplify types in general.
    pub fn is_trivially_true(&self) -> bool {
        self.is_true()
            || matches!(self.kind(), ExprKind::BinaryOp(BinOp::Eq | BinOp::Iff | BinOp::Imp, e1, e2) if e1.erase_spans() == e2.erase_spans())
    }

    /// Simple syntactic check to see if the expression is a trivially false predicate.
    pub fn is_trivially_false(&self) -> bool {
        self.is_false()
    }

    /// Whether the expression is *literally* the constant `true`.
    fn is_true(&self) -> bool {
        matches!(self.kind(), ExprKind::Constant(Constant::Bool(true)))
    }

    /// Whether the expression is *literally* the constant `false`.
    fn is_false(&self) -> bool {
        matches!(self.kind(), ExprKind::Constant(Constant::Bool(false)))
    }

    pub fn from_const(tcx: TyCtxt, c: &Const) -> Expr {
        match &c.kind {
            ConstKind::Param(param_const) => Expr::const_generic(*param_const),
            ConstKind::Value(ty, ValTree::Leaf(scalar)) => {
                Expr::constant(Constant::from_scalar_int(tcx, *scalar, ty).unwrap())
            }
            ConstKind::Value(_ty, ValTree::Branch(_)) => {
                bug!("todo: ValTree::Branch {c:?}")
            }
            // We should have normalized away the unevaluated constants
            ConstKind::Unevaluated(_) => bug!("unexpected `ConstKind::Unevaluated`"),

            ConstKind::Infer(_) => bug!("unexpected `ConstKind::Infer`"),
        }
    }

    fn const_op(op: &BinOp, c1: &Constant, c2: &Constant) -> Option<Constant> {
        match op {
            BinOp::Iff => c1.iff(c2),
            BinOp::Imp => c1.imp(c2),
            BinOp::Or => c1.or(c2),
            BinOp::And => c1.and(c2),
            BinOp::Gt(Sort::Int) => c1.gt(c2),
            BinOp::Ge(Sort::Int) => c1.ge(c2),
            BinOp::Lt(Sort::Int) => c2.gt(c1),
            BinOp::Le(Sort::Int) => c2.ge(c1),
            BinOp::Eq => Some(c1.eq(c2)),
            BinOp::Ne => Some(c1.ne(c2)),
            _ => None,
        }
    }

    /// Simplify the expression by removing double negations, short-circuiting boolean connectives and
    /// doing constant folding. Note that we also have [`TypeFoldable::normalize`] which applies beta
    /// reductions for tuples and abstractions.
    ///
    /// Additionally replaces any occurrences of elements in assumed_preds with True.
    pub fn simplify(&self, assumed_preds: &SnapshotMap<Expr, ()>) -> Expr {
        struct Simplify<'a> {
            assumed_preds: &'a SnapshotMap<Expr, ()>,
        }

        impl TypeFolder for Simplify<'_> {
            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if self.assumed_preds.get(&expr.erase_spans()).is_some() {
                    return Expr::tt();
                }
                let span = expr.span();
                match expr.kind() {
                    ExprKind::BinaryOp(op, e1, e2) => {
                        let e1 = e1.fold_with(self);
                        let e2 = e2.fold_with(self);
                        match (op, e1.kind(), e2.kind()) {
                            (BinOp::And, ExprKind::Constant(Constant::Bool(false)), _) => {
                                Expr::constant(Constant::Bool(false)).at_opt(e1.span())
                            }
                            (BinOp::And, _, ExprKind::Constant(Constant::Bool(false))) => {
                                Expr::constant(Constant::Bool(false)).at_opt(e2.span())
                            }
                            (BinOp::And, ExprKind::Constant(Constant::Bool(true)), _) => e2,
                            (BinOp::And, _, ExprKind::Constant(Constant::Bool(true))) => e1,
                            (op, ExprKind::Constant(c1), ExprKind::Constant(c2)) => {
                                if let Some(c) = Expr::const_op(op, c1, c2) {
                                    Expr::constant(c).at_opt(span.or(e2.span()))
                                } else {
                                    Expr::binary_op(op.clone(), e1, e2).at_opt(span)
                                }
                            }
                            _ => Expr::binary_op(op.clone(), e1, e2).at_opt(span),
                        }
                    }
                    ExprKind::UnaryOp(UnOp::Not, e) => {
                        let e = e.fold_with(self);
                        match e.kind() {
                            ExprKind::Constant(Constant::Bool(b)) => {
                                Expr::constant(Constant::Bool(!b))
                            }
                            ExprKind::UnaryOp(UnOp::Not, e) => e.clone(),
                            ExprKind::BinaryOp(BinOp::Eq, e1, e2) => {
                                Expr::binary_op(BinOp::Ne, e1, e2).at_opt(span)
                            }
                            _ => Expr::unary_op(UnOp::Not, e).at_opt(span),
                        }
                    }
                    ExprKind::IfThenElse(p, e1, e2) => {
                        let p = p.fold_with(self);
                        if p.is_trivially_true() {
                            e1.fold_with(self).at_opt(span)
                        } else if p.is_trivially_false() {
                            e2.fold_with(self).at_opt(span)
                        } else {
                            Expr::ite(p, e1.fold_with(self), e2.fold_with(self)).at_opt(span)
                        }
                    }
                    _ => expr.super_fold_with(self),
                }
            }
        }
        self.fold_with(&mut Simplify { assumed_preds })
    }

    pub fn to_loc(&self) -> Option<Loc> {
        match self.kind() {
            ExprKind::Local(local) => Some(Loc::Local(*local)),
            ExprKind::Var(var) => Some(Loc::Var(*var)),
            _ => None,
        }
    }

    pub fn to_path(&self) -> Option<Path> {
        let mut expr = self;
        let mut proj = vec![];
        while let ExprKind::PathProj(e, field) = expr.kind() {
            proj.push(*field);
            expr = e;
        }
        proj.reverse();
        Some(Path::new(expr.to_loc()?, proj))
    }

    /// Whether this is an aggregate expression with no fields.
    pub fn is_unit(&self) -> bool {
        matches!(self.kind(), ExprKind::Tuple(flds) if flds.is_empty())
            || matches!(self.kind(), ExprKind::Ctor(Ctor::Struct(_), flds) if flds.is_empty())
    }

    pub fn eta_expand_abs(&self, inputs: &BoundVariableKinds, output: Sort) -> Lambda {
        let args = (0..inputs.len())
            .map(|idx| Expr::bvar(INNERMOST, BoundVar::from_usize(idx), BoundReftKind::Anon))
            .collect();
        let body = Expr::app(self, List::empty(), args);
        Lambda::bind_with_vars(body, inputs.clone(), output)
    }

    /// Applies a field projection to an expression and optimistically try to beta reduce it
    pub fn proj_and_reduce(&self, proj: FieldProj) -> Expr {
        match self.kind() {
            ExprKind::Tuple(flds) | ExprKind::Ctor(Ctor::Struct(_), flds) => {
                flds[proj.field_idx() as usize].clone()
            }
            _ => Expr::field_proj(self.clone(), proj),
        }
    }

    pub fn visit_conj<'a>(&'a self, mut f: impl FnMut(&'a Expr)) {
        fn go<'a>(e: &'a Expr, f: &mut impl FnMut(&'a Expr)) {
            if let ExprKind::BinaryOp(BinOp::And, e1, e2) = e.kind() {
                go(e1, f);
                go(e2, f);
            } else {
                f(e);
            }
        }
        go(self, &mut f);
    }

    pub fn flatten_conjs(&self) -> Vec<&Expr> {
        let mut vec = vec![];
        self.visit_conj(|e| vec.push(e));
        vec
    }

    pub fn has_evars(&self) -> bool {
        struct HasEvars;

        impl TypeVisitor for HasEvars {
            type BreakTy = ();
            fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<Self::BreakTy> {
                if let ExprKind::Var(Var::EVar(_)) = expr.kind() {
                    ControlFlow::Break(())
                } else {
                    expr.super_visit_with(self)
                }
            }
        }

        self.visit_with(&mut HasEvars).is_break()
    }

    pub fn erase_spans(&self) -> Expr {
        struct SpanEraser;
        impl TypeFolder for SpanEraser {
            fn fold_expr(&mut self, e: &Expr) -> Expr {
                e.super_fold_with(self).at_opt(None)
            }
        }
        self.fold_with(&mut SpanEraser)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub struct ESpan {
    /// The top-level span information
    pub span: Span,
    /// The span for the (base) call-site for def-expanded spans
    pub base: Option<Span>,
}

impl ESpan {
    pub fn new(span: Span) -> Self {
        Self { span, base: None }
    }

    pub fn with_base(&self, espan: ESpan) -> Self {
        Self { span: self.span, base: Some(espan.span) }
    }
}

#[derive(
    Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug, TypeFoldable, TypeVisitable,
)]
pub enum BinOp {
    Iff,
    Imp,
    Or,
    And,
    Eq,
    Ne,
    Gt(Sort),
    Ge(Sort),
    Lt(Sort),
    Le(Sort),
    Add(Sort),
    Sub(Sort),
    Mul(Sort),
    Div(Sort),
    Mod(Sort),
    BitAnd(Sort),
    BitOr(Sort),
    BitXor(Sort),
    BitShl(Sort),
    BitShr(Sort),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Encodable, Debug, Decodable)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, TyEncodable, TyDecodable)]
pub enum Ctor {
    /// for indices represented as `struct` in the refinement logic (e.g. using `refined_by` annotations)
    Struct(DefId),
    /// for indices represented as  `enum` in the refinement logic (e.g. using `reflected` annotations)
    Enum(DefId, VariantIdx),
}

impl Ctor {
    pub fn def_id(&self) -> DefId {
        match self {
            Self::Struct(def_id) | Self::Enum(def_id, _) => *def_id,
        }
    }

    pub fn variant_idx(&self) -> VariantIdx {
        match self {
            Self::Struct(_) => FIRST_VARIANT,
            Self::Enum(_, variant_idx) => *variant_idx,
        }
    }

    fn is_enum(&self) -> bool {
        matches!(self, Self::Enum(..))
    }
}

/// # Primitive Properties
/// Given a primop `op` with signature `(t1,...,tn) -> t`
/// We define a refined type for `op` expressed as a `RuleMatcher`
///
/// ```text
/// op :: (x1: t1, ..., xn: tn) -> { t[op_val[op](x1,...,xn)] | op_rel[x1,...,xn] }
/// ```
/// That is, using two *uninterpreted functions* `op_val` and `op_rel` that respectively denote
/// 1. The _value_ of the primop, and
/// 2. Some invariant _relation_ that holds for the primop.
///
/// The latter can be extended by the user via a `property` definition, which allows us
/// to customize primops like `<<` with extra "facts" or lemmas. See `tests/tests/pos/surface/primops00.rs` for an example.
#[derive(Debug, Clone, TyEncodable, TyDecodable, PartialEq, Eq, Hash)]
pub enum InternalFuncKind {
    /// UIF representing the value of a primop
    Val(BinOp),
    /// UIF representing the relationship of a primop
    Rel(BinOp),
    // Conversions betweeen Sorts
    Cast,
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, PartialEq, Eq, Hash)]
pub enum SpecFuncKind {
    /// Theory symbols *interpreted* by the SMT solver
    Thy(liquid_fixpoint::ThyFunc),
    /// User-defined uninterpreted functions with no definition
    Uif(FluxDefId),
    /// User-defined functions with a body definition
    Def(FluxDefId),
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, Debug, TyDecodable)]
pub enum ExprKind {
    Var(Var),
    Local(Local),
    Constant(Constant),
    /// A rust constant. This can be either `DefKind::Const` or `DefKind::AssocConst`
    ConstDefId(DefId),
    BinaryOp(BinOp, Expr, Expr),
    GlobalFunc(SpecFuncKind),
    InternalFunc(InternalFuncKind),
    UnaryOp(UnOp, Expr),
    FieldProj(Expr, FieldProj),
    /// A variant used in the logic to represent a variant of an ADT as a pair of the `DefId` and variant-index
    Ctor(Ctor, List<Expr>),
    Tuple(List<Expr>),
    PathProj(Expr, FieldIdx),
    IfThenElse(Expr, Expr, Expr),
    KVar(KVar),
    Alias(AliasReft, List<Expr>),
    Let(Expr, Binder<Expr>),
    /// Function application. The syntax allows arbitrary expressions in function position, but in
    /// practice we are restricted by what's possible to encode in fixpoint. In a nutshell, we need
    /// to make sure that expressions that can't be encoded are eliminated before we generate the
    /// fixpoint constraint. Most notably, lambda abstractions have to be fully applied before
    /// encoding into fixpoint (except when they appear as an index at the top-level).
    App(Expr, List<SortArg>, List<Expr>),
    /// Lambda abstractions. They are purely syntactic and we don't encode them in the logic. As such,
    /// they have some syntactic restrictions that we must carefully maintain:
    ///
    /// 1. They can appear as an index at the top level.
    /// 2. We can only substitute an abstraction for a variable in function position (or as an index).
    ///    More generally, we need to partially evaluate expressions such that all abstractions in
    ///    non-index position are eliminated before encoding into fixpoint. Right now, the
    ///    implementation only evaluates abstractions that are immediately applied to arguments,
    ///    thus the restriction.
    Abs(Lambda),

    /// Bounded quantifiers `exists i in 0..4 { pred(i) }` and `forall i in 0..4 { pred(i) }`.
    BoundedQuant(fhir::QuantKind, fhir::Range, Binder<Expr>),
    /// A hole is an expression that must be inferred either *semantically* by generating a kvar or
    /// *syntactically* by generating an evar. Whether a hole can be inferred semantically or
    /// syntactically depends on the position it appears: only holes appearing in predicate position
    /// can be inferred with a kvar (provided it satisfies the fixpoint horn constraints) and only
    /// holes used as an index (a position that fully determines their value) can be inferred with
    /// an evar.
    ///
    /// Holes are implicitly defined in a scope, i.e., their solution could mention free and bound
    /// variables in this scope. This must be considered when generating an inference variables for
    /// them (either evar or kvar). In fact, the main reason we have holes is that we want to
    /// decouple the places where we generate holes (where we don't want to worry about the scope),
    /// and the places where we generate inference variable for them (where we do need to worry
    /// about the scope).
    Hole(HoleKind),
    ForAll(Binder<Expr>),
    /// Only for non-cuts solutions from fixpoint
    Exists(Binder<Expr>),
    /// Is the expression constructed from constructor of the given DefId (which should be `reflected` Enum)
    IsCtor(DefId, VariantIdx, Expr),
}

impl ExprKind {
    fn intern(self) -> Expr {
        Expr { kind: Interned::new(self), espan: None }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub enum AggregateKind {
    Tuple(usize),
    Adt(DefId),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub enum FieldProj {
    Tuple { arity: usize, field: u32 },
    Adt { def_id: DefId, field: u32 },
}

impl FieldProj {
    pub fn arity(&self, genv: GlobalEnv) -> QueryResult<usize> {
        match self {
            FieldProj::Tuple { arity, .. } => Ok(*arity),
            FieldProj::Adt { def_id, .. } => {
                Ok(genv.adt_sort_def_of(*def_id)?.struct_variant().fields())
            }
        }
    }

    pub fn field_idx(&self) -> u32 {
        match self {
            FieldProj::Tuple { field, .. } | FieldProj::Adt { field, .. } => *field,
        }
    }
}

/// The position where a [hole] appears. This determines how it will be inferred. This is related
/// to, but not the same as, an [`InferMode`].
///
/// [`InferMode`]: super::InferMode
/// [hole]: ExprKind::Hole
#[derive(
    Debug, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable,
)]
pub enum HoleKind {
    /// A hole in predicate position (e.g., the predicate in a [`TyKind::Constr`]). It will be
    /// inferred by generating a kvar.
    ///
    /// [`TyKind::Constr`]: super::TyKind::Constr
    Pred,
    /// A hole used as a refinement argument or index. It will be inferred by generating an evar.
    /// The expression filling the hole must have the provided sort.
    ///
    /// NOTE(nilehmann) we used to require the `Sort` for generating the evar because we needed it
    /// to eta-expand aggregate sorts. We've since removed this behavior but I'm keeping it here
    /// just in case. We could remove in case it becomes too problematic.
    Expr(Sort),
}

/// In theory a kvar is just an unknown predicate that can use some variables in scope. In practice,
/// fixpoint makes a difference between the first and the rest of the arguments, the first one being
/// the kvar's *self argument*. Fixpoint will only instantiate qualifiers that use the self argument.
/// Flux generalizes the self argument to be a list. We call the rest of the arguments the *scope*.
#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable)]
pub struct KVar {
    pub kvid: KVid,
    /// The number of arguments consider to be *self arguments*.
    pub self_args: usize,
    /// The list of *all* arguments with the self arguments at the beginning, i.e., the
    /// list of self arguments followed by the scope.
    pub args: List<Expr>,
}

#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Encodable, Decodable)]
pub struct EarlyReftParam {
    pub index: u32,
    pub name: Symbol,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Encodable, Decodable, Debug)]
pub struct BoundReft {
    pub var: BoundVar,
    pub kind: BoundReftKind,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, TyEncodable, TyDecodable)]
pub enum Var {
    Free(Name),
    Bound(DebruijnIndex, BoundReft),
    EarlyParam(EarlyReftParam),
    EVar(EVid),
    ConstGeneric(ParamConst),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, TyEncodable, TyDecodable)]
pub struct Path {
    pub loc: Loc,
    projection: List<FieldIdx>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, TyEncodable, TyDecodable)]
pub enum Loc {
    Local(Local),
    Var(Var),
}

newtype_index! {
    /// *E*xistential *v*ariable *id*
    #[debug_format = "?{}e"]
    #[orderable]
    #[encodable]
    pub struct EVid {}
}

newtype_index! {
    #[debug_format = "$k{}"]
    #[encodable]
    pub struct KVid {}
}

newtype_index! {
    #[debug_format = "a{}"]
    #[orderable]
    #[encodable]
    pub struct Name {}
}

impl KVar {
    pub fn new(kvid: KVid, self_args: usize, args: Vec<Expr>) -> Self {
        KVar { kvid, self_args, args: List::from_vec(args) }
    }

    fn self_args(&self) -> &[Expr] {
        &self.args[..self.self_args]
    }

    fn scope(&self) -> &[Expr] {
        &self.args[self.self_args..]
    }
}

impl Var {
    pub fn to_expr(&self) -> Expr {
        Expr::var(*self)
    }
}

impl Path {
    pub fn new(loc: Loc, projection: impl Into<List<FieldIdx>>) -> Path {
        Path { loc, projection: projection.into() }
    }

    pub fn projection(&self) -> &[FieldIdx] {
        &self.projection[..]
    }

    pub fn to_expr(&self) -> Expr {
        self.projection
            .iter()
            .fold(self.loc.to_expr(), |e, f| Expr::path_proj(e, *f))
    }

    pub fn to_loc(&self) -> Option<Loc> {
        if self.projection.is_empty() { Some(self.loc) } else { None }
    }
}

impl Loc {
    pub fn to_expr(&self) -> Expr {
        match self {
            Loc::Local(local) => Expr::local(*local),
            Loc::Var(var) => Expr::var(*var),
        }
    }
}

macro_rules! impl_ops {
    ($($op:ident: $method:ident),*) => {$(
        impl<Rhs> std::ops::$op<Rhs> for Expr
        where
            Rhs: Into<Expr>,
        {
            type Output = Expr;

            fn $method(self, rhs: Rhs) -> Self::Output {
                let sort = crate::rty::Sort::Int;
                Expr::binary_op(BinOp::$op(sort), self, rhs)
            }
        }

        impl<Rhs> std::ops::$op<Rhs> for &Expr
        where
            Rhs: Into<Expr>,
        {
            type Output = Expr;

            fn $method(self, rhs: Rhs) -> Self::Output {
                let sort = crate::rty::Sort::Int;
                Expr::binary_op(BinOp::$op(sort), self, rhs)
            }
        }
    )*};
}
impl_ops!(Add: add, Sub: sub, Mul: mul, Div: div);

impl From<i32> for Expr {
    fn from(value: i32) -> Self {
        Expr::constant(Constant::from(value))
    }
}

impl From<&Expr> for Expr {
    fn from(e: &Expr) -> Self {
        e.clone()
    }
}

impl From<Path> for Expr {
    fn from(path: Path) -> Self {
        path.to_expr()
    }
}

impl From<Name> for Expr {
    fn from(name: Name) -> Self {
        Expr::fvar(name)
    }
}

impl From<Var> for Expr {
    fn from(var: Var) -> Self {
        Expr::var(var)
    }
}

impl From<SpecFuncKind> for Expr {
    fn from(kind: SpecFuncKind) -> Self {
        Expr::global_func(kind)
    }
}

impl From<InternalFuncKind> for Expr {
    fn from(kind: InternalFuncKind) -> Self {
        Expr::internal_func(kind)
    }
}

impl From<Loc> for Path {
    fn from(loc: Loc) -> Self {
        Path::new(loc, vec![])
    }
}

impl From<Name> for Loc {
    fn from(name: Name) -> Self {
        Loc::Var(Var::Free(name))
    }
}

impl From<Local> for Loc {
    fn from(local: Local) -> Self {
        Loc::Local(local)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub struct Real(pub u128);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum Constant {
    Int(BigInt),
    Real(Real),
    Bool(bool),
    Str(Symbol),
    Char(char),
    BitVec(u128, u32),
}

impl Constant {
    pub const ZERO: Constant = Constant::Int(BigInt::ZERO);
    pub const ONE: Constant = Constant::Int(BigInt::ONE);
    pub const TRUE: Constant = Constant::Bool(true);

    fn to_bool(self) -> Option<bool> {
        match self {
            Constant::Bool(b) => Some(b),
            _ => None,
        }
    }

    fn to_int(self) -> Option<BigInt> {
        match self {
            Constant::Int(n) => Some(n),
            _ => None,
        }
    }

    pub fn iff(&self, other: &Constant) -> Option<Constant> {
        let b1 = self.to_bool()?;
        let b2 = other.to_bool()?;
        Some(Constant::Bool(b1 == b2))
    }

    pub fn imp(&self, other: &Constant) -> Option<Constant> {
        let b1 = self.to_bool()?;
        let b2 = other.to_bool()?;
        Some(Constant::Bool(!b1 || b2))
    }

    pub fn or(&self, other: &Constant) -> Option<Constant> {
        let b1 = self.to_bool()?;
        let b2 = other.to_bool()?;
        Some(Constant::Bool(b1 || b2))
    }

    pub fn and(&self, other: &Constant) -> Option<Constant> {
        let b1 = self.to_bool()?;
        let b2 = other.to_bool()?;
        Some(Constant::Bool(b1 && b2))
    }

    pub fn eq(&self, other: &Constant) -> Constant {
        Constant::Bool(*self == *other)
    }

    pub fn ne(&self, other: &Constant) -> Constant {
        Constant::Bool(*self != *other)
    }

    pub fn gt(&self, other: &Constant) -> Option<Constant> {
        let n1 = self.to_int()?;
        let n2 = other.to_int()?;
        Some(Constant::Bool(n1 > n2))
    }

    pub fn ge(&self, other: &Constant) -> Option<Constant> {
        let n1 = self.to_int()?;
        let n2 = other.to_int()?;
        Some(Constant::Bool(n1 >= n2))
    }

    pub fn from_scalar_int<'tcx, T>(tcx: TyCtxt<'tcx>, scalar: ScalarInt, t: &T) -> Option<Self>
    where
        T: ToRustc<'tcx, T = rustc_middle::ty::Ty<'tcx>>,
    {
        use rustc_middle::ty::TyKind;
        let ty = t.to_rustc(tcx);
        match ty.kind() {
            TyKind::Int(int_ty) => Some(Constant::from(scalar_to_int(tcx, scalar, *int_ty))),
            TyKind::Uint(uint_ty) => Some(Constant::from(scalar_to_uint(tcx, scalar, *uint_ty))),
            TyKind::Bool => {
                let b = scalar_to_bits(tcx, scalar, ty)?;
                Some(Constant::Bool(b != 0))
            }
            TyKind::Char => {
                let b = scalar_to_bits(tcx, scalar, ty)?;
                Some(Constant::Char(char::from_u32(b as u32)?))
            }
            _ => bug!(),
        }
    }

    /// See [`BigInt::int_min`]
    pub fn int_min(bit_width: u32) -> Constant {
        Constant::Int(BigInt::int_min(bit_width))
    }

    /// See [`BigInt::int_max`]
    pub fn int_max(bit_width: u32) -> Constant {
        Constant::Int(BigInt::int_max(bit_width))
    }

    /// See [`BigInt::uint_max`]
    pub fn uint_max(bit_width: u32) -> Constant {
        Constant::Int(BigInt::uint_max(bit_width))
    }
}

impl From<i32> for Constant {
    fn from(c: i32) -> Self {
        Constant::Int(c.into())
    }
}

impl From<usize> for Constant {
    fn from(u: usize) -> Self {
        Constant::Int(u.into())
    }
}

impl From<u32> for Constant {
    fn from(c: u32) -> Self {
        Constant::Int(c.into())
    }
}

impl From<u128> for Constant {
    fn from(c: u128) -> Self {
        Constant::Int(c.into())
    }
}

impl From<i128> for Constant {
    fn from(c: i128) -> Self {
        Constant::Int(c.into())
    }
}

impl From<bool> for Constant {
    fn from(b: bool) -> Self {
        Constant::Bool(b)
    }
}

impl From<Symbol> for Constant {
    fn from(s: Symbol) -> Self {
        Constant::Str(s)
    }
}

impl From<char> for Constant {
    fn from(c: char) -> Self {
        Constant::Char(c)
    }
}

impl_internable!(ExprKind);
impl_slice_internable!(Expr, KVar);

#[derive(Debug)]
pub struct FieldBind<T> {
    pub name: Symbol,
    pub value: T,
}

impl<T: Pretty> Pretty for FieldBind<T> {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        w!(cx, f, "{}: {:?}", ^self.name, &self.value)
    }
}

pub(crate) mod pretty {
    use flux_rustc_bridge::def_id_to_string;

    use super::*;
    use crate::{name_of_thy_func, rty::pretty::nested_with_bound_vars};

    #[derive(PartialEq, Eq, PartialOrd, Ord)]
    enum Precedence {
        Iff,
        Imp,
        Or,
        And,
        Cmp,
        Bitvec,
        AddSub,
        MulDiv,
    }

    impl BinOp {
        fn precedence(&self) -> Precedence {
            match self {
                BinOp::Iff => Precedence::Iff,
                BinOp::Imp => Precedence::Imp,
                BinOp::Or => Precedence::Or,
                BinOp::And => Precedence::And,
                BinOp::Eq
                | BinOp::Ne
                | BinOp::Gt(_)
                | BinOp::Lt(_)
                | BinOp::Ge(_)
                | BinOp::Le(_) => Precedence::Cmp,
                BinOp::Add(_) | BinOp::Sub(_) => Precedence::AddSub,
                BinOp::Mul(_) | BinOp::Div(_) | BinOp::Mod(_) => Precedence::MulDiv,
                BinOp::BitAnd(_)
                | BinOp::BitOr(_)
                | BinOp::BitShl(_)
                | BinOp::BitShr(_)
                | BinOp::BitXor(_) => Precedence::Bitvec,
            }
        }
    }

    impl Precedence {
        pub fn is_associative(&self) -> bool {
            !matches!(self, Precedence::Imp | Precedence::Cmp)
        }
    }

    pub fn should_parenthesize(op: &BinOp, child: &Expr) -> bool {
        if let ExprKind::BinaryOp(child_op, ..) = child.kind() {
            child_op.precedence() < op.precedence()
                || (child_op.precedence() == op.precedence() && !op.precedence().is_associative())
        } else {
            false
        }
    }

    impl Pretty for Ctor {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Ctor::Struct(def_id) => {
                    w!(cx, f, "{:?}", def_id)
                }
                Ctor::Enum(def_id, variant_idx) => {
                    w!(cx, f, "{:?}::{:?}", def_id, ^variant_idx)
                }
            }
        }
    }

    impl Pretty for fhir::QuantKind {
        fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                fhir::QuantKind::Exists => w!(cx, f, "∃"),
                fhir::QuantKind::Forall => w!(cx, f, "∀"),
            }
        }
    }

    impl Pretty for InternalFuncKind {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                InternalFuncKind::Val(op) => w!(cx, f, "[{:?}]", op),
                InternalFuncKind::Rel(op) => w!(cx, f, "[{:?}]?", op),
                InternalFuncKind::Cast => w!(cx, f, "cast"),
            }
        }
    }

    impl Pretty for Expr {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let e = if cx.simplify_exprs {
                self.simplify(&SnapshotMap::default())
            } else {
                self.clone()
            };
            match e.kind() {
                ExprKind::Var(var) => w!(cx, f, "{:?}", var),
                ExprKind::Local(local) => w!(cx, f, "{:?}", ^local),
                ExprKind::ConstDefId(did) => w!(cx, f, "{}", ^def_id_to_string(*did)),
                ExprKind::Constant(c) => w!(cx, f, "{:?}", c),

                ExprKind::BinaryOp(op, e1, e2) => {
                    if should_parenthesize(op, e1) {
                        w!(cx, f, "({:?})", e1)?;
                    } else {
                        w!(cx, f, "{:?}", e1)?;
                    }
                    if matches!(op, BinOp::Div(_)) {
                        w!(cx, f, "{:?}", op)?;
                    } else {
                        w!(cx, f, " {:?} ", op)?;
                    }
                    if should_parenthesize(op, e2) {
                        w!(cx, f, "({:?})", e2)?;
                    } else {
                        w!(cx, f, "{:?}", e2)?;
                    }
                    Ok(())
                }
                ExprKind::UnaryOp(op, e) => {
                    if e.is_atom() {
                        w!(cx, f, "{:?}{:?}", op, e)
                    } else {
                        w!(cx, f, "{:?}({:?})", op, e)
                    }
                }
                ExprKind::FieldProj(e, proj) if let ExprKind::Ctor(_, _) = e.kind() => {
                    // special case to avoid printing `{n:12}.n` as `12.n` but instead, just print `12`
                    // TODO: maintain an invariant that `FieldProj` never has a Ctor as first argument (as always reduced)
                    w!(cx, f, "{:?}", e.proj_and_reduce(*proj))
                }
                ExprKind::FieldProj(e, proj) => {
                    if e.is_atom() {
                        w!(cx, f, "{:?}.{}", e, ^fmt_field_proj(cx, *proj))
                    } else {
                        w!(cx, f, "({:?}).{}", e, ^fmt_field_proj(cx, *proj))
                    }
                }
                ExprKind::Tuple(flds) => {
                    if let [e] = &flds[..] {
                        w!(cx, f, "({:?},)", e)
                    } else {
                        w!(cx, f, "({:?})", join!(", ", flds))
                    }
                }
                ExprKind::IsCtor(def_id, variant_idx, idx) => {
                    w!(cx, f, "({:?} is {:?}::{:?})", idx, def_id, ^variant_idx)
                }
                ExprKind::Ctor(ctor, flds) => {
                    let def_id = ctor.def_id();
                    if let Some(adt_sort_def) = cx.adt_sort_def_of(def_id) {
                        let variant = adt_sort_def.variant(ctor.variant_idx()).field_names();
                        let fields = iter::zip(variant, flds)
                            .map(|(name, value)| FieldBind { name: *name, value: value.clone() })
                            .collect_vec();
                        match ctor {
                            Ctor::Struct(_) => {
                                w!(cx, f, "{:?} {{ {:?} }}", def_id, join!(", ", fields))
                            }
                            Ctor::Enum(_, idx) => {
                                if fields.is_empty() {
                                    w!(cx, f, "{:?}::{:?}", def_id, ^idx.index())
                                } else {
                                    w!(cx, f, "{:?}::{:?}({:?})", def_id, ^idx.index(), join!(", ", fields))
                                }
                            }
                        }
                    } else {
                        match ctor {
                            Ctor::Struct(_) => {
                                w!(cx, f, "{:?} {{ {:?} }}", def_id, join!(", ", flds))
                            }
                            Ctor::Enum(_, idx) => {
                                w!(cx, f, "{:?}::{:?} {{ {:?} }}", def_id, ^idx, join!(", ", flds))
                            }
                        }
                    }
                }
                ExprKind::PathProj(e, field) => {
                    if e.is_atom() {
                        w!(cx, f, "{:?}.{:?}", e, field)
                    } else {
                        w!(cx, f, "({:?}).{:?}", e, field)
                    }
                }
                ExprKind::App(func, _, args) => {
                    w!(cx, f, "{:?}({})",
                        parens!(func, !func.is_atom()),
                        ^args
                            .iter()
                            .format_with(", ", |arg, f| f(&format_args_cx!(cx, "{:?}", arg)))
                    )
                }
                ExprKind::IfThenElse(p, e1, e2) => {
                    w!(cx, f, "if {:?} {{ {:?} }} else {{ {:?} }}", p, e1, e2)
                }
                ExprKind::Hole(_) => {
                    w!(cx, f, "*")
                }
                ExprKind::KVar(kvar) => {
                    w!(cx, f, "{:?}", kvar)
                }
                ExprKind::Alias(alias, args) => {
                    w!(cx, f, "{:?}({:?})", alias, join!(", ", args))
                }
                ExprKind::Abs(lam) => {
                    w!(cx, f, "{:?}", lam)
                }
                ExprKind::GlobalFunc(SpecFuncKind::Def(did) | SpecFuncKind::Uif(did)) => {
                    w!(cx, f, "{}", ^did.name())
                }
                ExprKind::GlobalFunc(SpecFuncKind::Thy(itf)) => {
                    if let Some(name) = name_of_thy_func(*itf) {
                        w!(cx, f, "{}", ^name)
                    } else {
                        w!(cx, f, "<error>")
                    }
                }
                ExprKind::InternalFunc(func) => {
                    w!(cx, f, "{:?}", func)
                }
                ExprKind::ForAll(expr) => {
                    let vars = expr.vars();
                    cx.with_bound_vars(vars, || {
                        if !vars.is_empty() {
                            cx.fmt_bound_vars(false, "∀", vars, ". ", f)?;
                        }
                        w!(cx, f, "{:?}", expr.skip_binder_ref())
                    })
                }
                ExprKind::Exists(expr) => {
                    let vars = expr.vars();
                    cx.with_bound_vars(vars, || {
                        if !vars.is_empty() {
                            cx.fmt_bound_vars(false, "∃", vars, ". ", f)?;
                        }
                        w!(cx, f, "{:?}", expr.skip_binder_ref())
                    })
                }
                ExprKind::BoundedQuant(kind, rng, body) => {
                    let vars = body.vars();
                    cx.with_bound_vars(vars, || {
                        w!(
                            cx,
                            f,
                            "{:?} {}..{} {{ {:?} }}",
                            kind,
                            ^rng.start,
                            ^rng.end,
                            body.skip_binder_ref()
                        )
                    })
                }
                ExprKind::Let(init, body) => {
                    let vars = body.vars();
                    cx.with_bound_vars(vars, || {
                        cx.fmt_bound_vars(false, "(let ", vars, " = ", f)?;
                        w!(cx, f, "{:?} in {:?})", init, body.skip_binder_ref())
                    })
                }
            }
        }
    }

    fn fmt_field_proj(cx: &PrettyCx, proj: FieldProj) -> String {
        if let FieldProj::Adt { def_id, field } = proj
            && let Some(adt_sort_def) = cx.adt_sort_def_of(def_id)
        {
            format!("{}", adt_sort_def.struct_variant().field_names()[field as usize])
        } else {
            format!("{}", proj.field_idx())
        }
    }

    impl Pretty for Constant {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Constant::Int(i) => w!(cx, f, "{i}"),
                Constant::BitVec(i, sz) => w!(cx, f, "bv({i}, {sz})"),
                Constant::Real(r) => w!(cx, f, "{}.0", ^r.0),
                Constant::Bool(b) => w!(cx, f, "{b}"),
                Constant::Str(sym) => w!(cx, f, "\"{sym}\""),
                Constant::Char(c) => w!(cx, f, "\'{c}\'"),
            }
        }
    }

    impl Pretty for AliasReft {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            w!(cx, f, "<({:?}) as {:?}", &self.args[0], self.assoc_id.parent())?;
            let args = &self.args[1..];
            if !args.is_empty() {
                w!(cx, f, "<{:?}>", join!(", ", args))?;
            }
            w!(cx, f, ">::{}", ^self.assoc_id.name())
        }
    }

    impl Pretty for Lambda {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let vars = self.body.vars();
            // TODO: remove redundant vars; see Ty
            // let redundant_bvars = self.body.redundant_bvars().into_iter().collect();
            cx.with_bound_vars(vars, || {
                cx.fmt_bound_vars(false, "λ", vars, ". ", f)?;
                w!(cx, f, "{:?}", self.body.as_ref().skip_binder())
            })
        }
    }

    impl Pretty for Var {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Var::Bound(debruijn, var) => cx.fmt_bound_reft(*debruijn, *var, f),
                Var::EarlyParam(var) => w!(cx, f, "{}", ^var.name),
                Var::Free(name) => w!(cx, f, "{:?}", ^name),
                Var::EVar(evar) => w!(cx, f, "{:?}", ^evar),
                Var::ConstGeneric(param) => w!(cx, f, "{}", ^param.name),
            }
        }
    }

    impl Pretty for KVar {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            w!(cx, f, "{:?}", ^self.kvid)?;
            match cx.kvar_args {
                KVarArgs::All => {
                    w!(
                        cx,
                        f,
                        "({:?})[{:?}]",
                        join!(", ", self.self_args()),
                        join!(", ", self.scope())
                    )?;
                }
                KVarArgs::SelfOnly => w!(cx, f, "({:?})", join!(", ", self.self_args()))?,
                KVarArgs::Hide => {}
            }
            Ok(())
        }
    }

    impl Pretty for Path {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            w!(cx, f, "{:?}", &self.loc)?;
            for field in &self.projection {
                w!(cx, f, ".{}", ^u32::from(*field))?;
            }
            Ok(())
        }
    }

    impl Pretty for Loc {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Loc::Local(local) => w!(cx, f, "{:?}", ^local),
                Loc::Var(var) => w!(cx, f, "{:?}", var),
            }
        }
    }

    impl Pretty for BinOp {
        fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                BinOp::Iff => w!(cx, f, "⇔"),
                BinOp::Imp => w!(cx, f, "⇒"),
                BinOp::Or => w!(cx, f, "∨"),
                BinOp::And => w!(cx, f, "∧"),
                BinOp::Eq => w!(cx, f, "="),
                BinOp::Ne => w!(cx, f, "≠"),
                BinOp::Gt(_) => w!(cx, f, ">"),
                BinOp::Ge(_) => w!(cx, f, "≥"),
                BinOp::Lt(_) => w!(cx, f, "<"),
                BinOp::Le(_) => w!(cx, f, "≤"),
                BinOp::Add(_) => w!(cx, f, "+"),
                BinOp::Sub(_) => w!(cx, f, "-"),
                BinOp::Mul(_) => w!(cx, f, "*"),
                BinOp::Div(_) => w!(cx, f, "/"),
                BinOp::Mod(_) => w!(cx, f, "mod"),
                BinOp::BitAnd(_) => w!(cx, f, "&"),
                BinOp::BitOr(_) => w!(cx, f, "|"),
                BinOp::BitXor(_) => w!(cx, f, "^"),
                BinOp::BitShl(_) => w!(cx, f, "<<"),
                BinOp::BitShr(_) => w!(cx, f, ">>"),
            }
        }
    }

    impl Pretty for UnOp {
        fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                UnOp::Not => w!(cx, f, "¬"),
                UnOp::Neg => w!(cx, f, "-"),
            }
        }
    }

    impl_debug_with_default_cx!(Expr, Loc, Path, Var, KVar, Lambda, AliasReft);

    impl PrettyNested for Lambda {
        fn fmt_nested(&self, cx: &PrettyCx) -> Result<NestedString, fmt::Error> {
            // TODO: remove redundant vars; see Ty
            nested_with_bound_vars(cx, "λ", self.body.vars(), None, |prefix| {
                let expr_d = self.body.skip_binder_ref().fmt_nested(cx)?;
                let text = format!("{}{}", prefix, expr_d.text);
                Ok(NestedString { text, children: expr_d.children, key: None })
            })
        }
    }

    pub fn aggregate_nested(
        cx: &PrettyCx,
        ctor: &Ctor,
        flds: &[Expr],
        is_named: bool,
    ) -> Result<NestedString, fmt::Error> {
        let def_id = ctor.def_id();
        let mut text =
            if is_named && ctor.is_enum() { format_cx!(cx, "{:?}", ctor) } else { "".to_string() };
        if flds.is_empty() {
            // No fields, no index
            Ok(NestedString { text, children: None, key: None })
        } else if flds.len() == 1 {
            // Single field, inline index
            text += &format_cx!(cx, "{:?}", flds[0].clone());
            Ok(NestedString { text, children: None, key: None })
        } else {
            let keys = if let Some(adt_sort_def) = cx.adt_sort_def_of(def_id) {
                adt_sort_def
                    .variant(ctor.variant_idx())
                    .field_names()
                    .iter()
                    .map(|name| format!("{name}"))
                    .collect_vec()
            } else {
                (0..flds.len()).map(|i| format!("arg{i}")).collect_vec()
            };
            // Multiple fields, nested index
            text += "{..}";
            let mut children = vec![];
            for (key, fld) in iter::zip(keys, flds) {
                let fld_d = fld.fmt_nested(cx)?;
                children.push(NestedString { key: Some(key), ..fld_d });
            }
            Ok(NestedString { text, children: Some(children), key: None })
        }
    }

    impl PrettyNested for Expr {
        fn fmt_nested(&self, cx: &PrettyCx) -> Result<NestedString, fmt::Error> {
            let e = if cx.simplify_exprs {
                self.simplify(&SnapshotMap::default())
            } else {
                self.clone()
            };
            match e.kind() {
                ExprKind::Var(..)
                | ExprKind::Local(..)
                | ExprKind::Constant(..)
                | ExprKind::ConstDefId(..)
                | ExprKind::Hole(..)
                | ExprKind::GlobalFunc(..)
                | ExprKind::InternalFunc(..)
                | ExprKind::KVar(..) => debug_nested(cx, &e),

                ExprKind::IfThenElse(p, e1, e2) => {
                    let p_d = p.fmt_nested(cx)?;
                    let e1_d = e1.fmt_nested(cx)?;
                    let e2_d = e2.fmt_nested(cx)?;
                    let text = format!("(if {} then {} else {})", p_d.text, e1_d.text, e2_d.text);
                    let children = float_children(vec![p_d.children, e1_d.children, e2_d.children]);
                    Ok(NestedString { text, children, key: None })
                }
                ExprKind::BinaryOp(op, e1, e2) => {
                    let e1_d = e1.fmt_nested(cx)?;
                    let e2_d = e2.fmt_nested(cx)?;
                    let e1_text = if should_parenthesize(op, e1) {
                        format!("({})", e1_d.text)
                    } else {
                        e1_d.text
                    };
                    let e2_text = if should_parenthesize(op, e2) {
                        format!("({})", e2_d.text)
                    } else {
                        e2_d.text
                    };
                    let op_d = debug_nested(cx, op)?;
                    let op_text = if matches!(op, BinOp::Div(_)) {
                        op_d.text
                    } else {
                        format!(" {} ", op_d.text)
                    };
                    let text = format!("{e1_text}{op_text}{e2_text}");
                    let children = float_children(vec![e1_d.children, e2_d.children]);
                    Ok(NestedString { text, children, key: None })
                }
                ExprKind::UnaryOp(op, e) => {
                    let e_d = e.fmt_nested(cx)?;
                    let op_d = debug_nested(cx, op)?;
                    let text = if e.is_atom() {
                        format!("{}{}", op_d.text, e_d.text)
                    } else {
                        format!("{}({})", op_d.text, e_d.text)
                    };
                    Ok(NestedString { text, children: e_d.children, key: None })
                }
                ExprKind::FieldProj(e, proj) if let ExprKind::Ctor(_, _) = e.kind() => {
                    // special case to avoid printing `{n:12}.n` as `12.n` but instead, just print `12`
                    // TODO: maintain an invariant that `FieldProj` never has a Ctor as first argument (as always reduced)
                    e.proj_and_reduce(*proj).fmt_nested(cx)
                }
                ExprKind::FieldProj(e, proj) => {
                    let e_d = e.fmt_nested(cx)?;
                    let text = if e.is_atom() {
                        format!("{}.{}", e_d.text, fmt_field_proj(cx, *proj))
                    } else {
                        format!("({}).{}", e_d.text, fmt_field_proj(cx, *proj))
                    };
                    Ok(NestedString { text, children: e_d.children, key: None })
                }
                ExprKind::Tuple(flds) => {
                    let mut texts = vec![];
                    let mut kidss = vec![];
                    for e in flds {
                        let e_d = e.fmt_nested(cx)?;
                        texts.push(e_d.text);
                        kidss.push(e_d.children);
                    }
                    let text = if let [e] = &texts[..] {
                        format!("({e},)")
                    } else {
                        format!("({})", texts.join(", "))
                    };
                    let children = float_children(kidss);
                    Ok(NestedString { text, children, key: None })
                }
                ExprKind::Ctor(ctor, flds) => aggregate_nested(cx, ctor, flds, true),
                ExprKind::IsCtor(def_id, variant_idx, idx) => {
                    let text = format!("is::{:?}::{:?}( {:?} )", def_id, variant_idx, idx);
                    Ok(NestedString { text, children: None, key: None })
                }
                ExprKind::PathProj(e, field) => {
                    let e_d = e.fmt_nested(cx)?;
                    let text = if e.is_atom() {
                        format!("{}.{:?}", e_d.text, field)
                    } else {
                        format!("({}).{:?}", e_d.text, field)
                    };
                    Ok(NestedString { text, children: e_d.children, key: None })
                }
                ExprKind::Alias(alias, args) => {
                    let mut texts = vec![];
                    let mut kidss = vec![];
                    for arg in args {
                        let arg_d = arg.fmt_nested(cx)?;
                        texts.push(arg_d.text);
                        kidss.push(arg_d.children);
                    }
                    let text = format_cx!(cx, "{:?}({:?})", alias, texts.join(", "));
                    let children = float_children(kidss);
                    Ok(NestedString { text, children, key: None })
                }
                ExprKind::App(func, _, args) => {
                    let func_d = func.fmt_nested(cx)?;
                    let mut texts = vec![];
                    let mut kidss = vec![func_d.children];
                    for arg in args {
                        let arg_d = arg.fmt_nested(cx)?;
                        texts.push(arg_d.text);
                        kidss.push(arg_d.children);
                    }
                    let text = if func.is_atom() {
                        format!("{}({})", func_d.text, texts.join(", "))
                    } else {
                        format!("({})({})", func_d.text, texts.join(", "))
                    };
                    let children = float_children(kidss);
                    Ok(NestedString { text, children, key: None })
                }
                ExprKind::Abs(lambda) => lambda.fmt_nested(cx),
                ExprKind::Let(init, body) => {
                    // FIXME this is very wrong!
                    nested_with_bound_vars(cx, "let", body.vars(), None, |prefix| {
                        let body = body.skip_binder_ref().fmt_nested(cx)?;
                        let text = format!("{:?} {}{}", init, prefix, body.text);
                        Ok(NestedString { text, children: body.children, key: None })
                    })
                }
                ExprKind::BoundedQuant(kind, rng, body) => {
                    let left = match kind {
                        fhir::QuantKind::Forall => "∀",
                        fhir::QuantKind::Exists => "∃",
                    };
                    let right = Some(format!(" in {}..{}", rng.start, rng.end));

                    nested_with_bound_vars(cx, left, body.vars(), right, |all_str| {
                        let expr_d = body.as_ref().skip_binder().fmt_nested(cx)?;
                        let text = format!("{}{}", all_str, expr_d.text);
                        Ok(NestedString { text, children: expr_d.children, key: None })
                    })
                }
                ExprKind::ForAll(expr) => {
                    nested_with_bound_vars(cx, "∀", expr.vars(), None, |all_str| {
                        let expr_d = expr.as_ref().skip_binder().fmt_nested(cx)?;
                        let text = format!("{}{}", all_str, expr_d.text);
                        Ok(NestedString { text, children: expr_d.children, key: None })
                    })
                }
                ExprKind::Exists(expr) => {
                    nested_with_bound_vars(cx, "∀", expr.vars(), None, |all_str| {
                        let expr_d = expr.as_ref().skip_binder().fmt_nested(cx)?;
                        let text = format!("{}{}", all_str, expr_d.text);
                        Ok(NestedString { text, children: expr_d.children, key: None })
                    })
                }
            }
        }
    }
}
