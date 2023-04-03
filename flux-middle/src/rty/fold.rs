//! This modules folows the implementation of folding in rustc. For more information read the
//! documentation in [`rustc_middle::ty::fold`].

use flux_common::bug;
use itertools::Itertools;
use rustc_hash::FxHashSet;

use super::{
    evars::EVarSol,
    normalize::{Defns, Normalizer},
    subst::EVarSubstFolder,
    BaseTy, Binder, Constraint, DebruijnIndex, Expr, ExprKind, FnOutput, FnSig, FnTraitPredicate,
    FuncSort, GenericArg, Index, Invariant, KVar, Name, Opaqueness, PolyFnSig, Predicate,
    Qualifier, Sort, Ty, TyKind, INNERMOST,
};
use crate::{
    intern::{Internable, List},
    rty::{Var, VariantDef},
};

pub trait TypeVisitor: Sized {
    fn visit_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) {
        t.super_visit_with(self);
    }

    fn visit_expr(&mut self, expr: &Expr) {
        expr.super_visit_with(self);
    }

    fn visit_fvar(&mut self, _name: Name) {}

    fn visit_ty(&mut self, ty: &Ty) {
        ty.super_visit_with(self);
    }

    fn visit_bty(&mut self, bty: &BaseTy) {
        bty.super_visit_with(self);
    }
}

pub trait TypeFolder: Sized {
    fn fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Binder<T> {
        t.super_fold_with(self)
    }

    fn fold_sort(&mut self, sort: &Sort) -> Sort {
        sort.super_fold_with(self)
    }

    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        ty.super_fold_with(self)
    }

    fn fold_bty(&mut self, bty: &BaseTy) -> BaseTy {
        bty.super_fold_with(self)
    }

    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        expr.super_fold_with(self)
    }
}

pub trait TypeFoldable: Sized {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self;
    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V);

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        self.super_fold_with(folder)
    }

    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.super_visit_with(visitor);
    }

    /// Normalize expressions by applying beta reductions for tuples and lambda abstractions.
    fn normalize(&self, defns: &Defns) -> Self {
        self.fold_with(&mut Normalizer::new(defns))
    }

    /// Returns the set of all free variables.
    /// For example, `Vec<i32[n]>{v : v > m}` returns `{n, m}`.
    fn fvars(&self) -> FxHashSet<Name> {
        struct CollectFreeVars(FxHashSet<Name>);

        impl TypeVisitor for CollectFreeVars {
            fn visit_fvar(&mut self, name: Name) {
                self.0.insert(name);
            }
        }

        let mut collector = CollectFreeVars(FxHashSet::default());
        self.visit_with(&mut collector);
        collector.0
    }

    /// Replaces all [`holes`] with a fresh predicate generated by calling `mk_pred`. The function
    /// `mk_pred` takes a list with the sorts of all bound variables at the point the hole was found.
    /// The list is ordered from outermost to innermost binder, i.e., the last element is the binder
    /// closest to the hole.
    ///
    /// [`holes`]: ExprKind::Hole
    fn replace_holes(&self, mk_pred: impl FnMut(&[Sort]) -> Expr) -> Self {
        struct ReplaceHoles<F>(F, Vec<Sort>);

        impl<F> TypeFolder for ReplaceHoles<F>
        where
            F: FnMut(&[Sort]) -> Expr,
        {
            fn fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Binder<T> {
                self.1.push(t.sort().clone());
                let t = t.super_fold_with(self);
                self.1.pop();
                t
            }

            fn fold_expr(&mut self, e: &Expr) -> Expr {
                if let ExprKind::Hole = e.kind() {
                    self.0(&self.1)
                } else {
                    e.super_fold_with(self)
                }
            }
        }

        self.fold_with(&mut ReplaceHoles(mk_pred, vec![]))
    }

    /// Turns each [`TyKind::Indexed`] into [`TyKind::Exists`] with a [`hole`] and replaces
    /// all existing predicates with a [`hole`].
    /// For example, `Vec<{v. i32[v] | v > 0}>[n]` becomes `{n. Vec<{v. i32[v] | *}>[n] | *}`.
    ///
    /// [`hole`]: ExprKind::Hole
    fn with_holes(&self) -> Self {
        struct WithHoles {
            in_exists: bool,
        }

        impl TypeFolder for WithHoles {
            fn fold_ty(&mut self, ty: &Ty) -> Ty {
                match ty.kind() {
                    TyKind::Indexed(bty, _) => {
                        if self.in_exists {
                            ty.super_fold_with(self)
                        } else {
                            Ty::exists_with_constr(bty.fold_with(self), Expr::hole())
                        }
                    }
                    TyKind::Exists(ty) => {
                        Ty::exists(ty.fold_with(&mut WithHoles { in_exists: true }))
                    }
                    TyKind::Constr(_, ty) => Ty::constr(Expr::hole(), ty.fold_with(self)),
                    _ => ty.super_fold_with(self),
                }
            }
        }

        self.fold_with(&mut WithHoles { in_exists: false })
    }

    fn replace_evars(&self, evars: &EVarSol) -> Self {
        self.fold_with(&mut EVarSubstFolder::new(evars))
            .normalize(&Default::default())
    }

    fn shift_in_escaping(&self, amount: u32) -> Self {
        struct Shifter {
            current_index: DebruijnIndex,
            amount: u32,
        }

        impl TypeFolder for Shifter {
            fn fold_binder<T>(&mut self, t: &Binder<T>) -> Binder<T>
            where
                T: TypeFoldable,
            {
                self.current_index.shift_in(1);
                let r = t.super_fold_with(self);
                self.current_index.shift_out(1);
                r
            }

            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::Var(Var::LateBound(debruijn)) = expr.kind()
                    && *debruijn >= self.current_index
                {
                    Expr::late_bvar(debruijn.shifted_in(self.amount))
                } else {
                    expr.super_fold_with(self)
                }
            }
        }
        self.fold_with(&mut Shifter { amount, current_index: INNERMOST })
    }

    fn shift_out_escaping(&self, amount: u32) -> Self {
        struct Shifter {
            amount: u32,
            current_index: DebruijnIndex,
        }

        impl TypeFolder for Shifter {
            fn fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Binder<T> {
                self.current_index.shift_in(1);
                let t = t.super_fold_with(self);
                self.current_index.shift_out(1);
                t
            }

            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::Var(Var::LateBound(debruijn)) = expr.kind()
                    && debruijn >= &self.current_index
                {
                    Expr::late_bvar(debruijn.shifted_out(self.amount))
                } else {
                    expr.super_fold_with(self)
                }
            }
        }
        self.fold_with(&mut Shifter { amount, current_index: INNERMOST })
    }

    fn has_escaping_bvars(&self) -> bool {
        struct HasEscapingVars {
            /// Anything bound by `outer_index` or "above" is escaping.
            outer_index: DebruijnIndex,
            found: bool,
        }

        impl TypeVisitor for HasEscapingVars {
            fn visit_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) {
                self.outer_index.shift_in(1);
                t.super_visit_with(self);
                self.outer_index.shift_out(1);
            }

            // TODO(nilehmann) keep track of the outermost binder to optimize this, i.e.,
            // what rustc calls outer_exclusive_binder.
            fn visit_expr(&mut self, expr: &Expr) {
                if let ExprKind::Var(Var::LateBound(debruijn)) = expr.kind() {
                    if *debruijn >= self.outer_index {
                        self.found = true;
                    }
                } else {
                    expr.super_visit_with(self);
                }
            }
        }
        let mut visitor = HasEscapingVars { outer_index: INNERMOST, found: false };
        self.visit_with(&mut visitor);
        visitor.found
    }
}

impl TypeFoldable for Predicate {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            Predicate::FnTrait(pred) => Predicate::FnTrait(pred.fold_with(folder)),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self {
            Predicate::FnTrait(pred) => pred.visit_with(visitor),
        }
    }
}

impl TypeFoldable for FnTraitPredicate {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        FnTraitPredicate {
            bounded_ty: self.bounded_ty.fold_with(folder),
            tupled_args: self.tupled_args.fold_with(folder),
            output: self.output.fold_with(folder),
            kind: self.kind,
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.bounded_ty.visit_with(visitor);
        self.tupled_args.visit_with(visitor);
        self.output.visit_with(visitor);
    }
}

impl TypeFoldable for Sort {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            Sort::Tuple(sorts) => Sort::tuple(sorts.fold_with(folder)),
            Sort::Func(fsort) => {
                Sort::Func(FuncSort { input_and_output: fsort.input_and_output.fold_with(folder) })
            }
            Sort::Int
            | Sort::Bool
            | Sort::Real
            | Sort::Loc
            | Sort::BitVec(_)
            | Sort::Param(_)
            | Sort::User(_) => self.clone(),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self {
            Sort::Tuple(sorts) => sorts.visit_with(visitor),
            Sort::Func(fsort) => fsort.input_and_output.visit_with(visitor),
            Sort::Int
            | Sort::Bool
            | Sort::Real
            | Sort::BitVec(_)
            | Sort::Loc
            | Sort::Param(_)
            | Sort::User(_) => {}
        }
    }

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        folder.fold_sort(self)
    }
}

impl<T> TypeFoldable for Binder<T>
where
    T: TypeFoldable,
{
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        Binder::new(self.value.fold_with(folder), self.sort.fold_with(folder))
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.value.visit_with(visitor);
    }

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        folder.fold_binder(self)
    }

    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        visitor.visit_binder(self);
    }
}

impl TypeFoldable for PolyFnSig {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        PolyFnSig { fn_sig: self.fn_sig.fold_with(folder), modes: self.modes.clone() }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.fn_sig.visit_with(visitor);
    }
}

impl TypeFoldable for VariantDef {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        let fields = self
            .fields
            .iter()
            .map(|ty| ty.fold_with(folder))
            .collect_vec();
        let ret = self.ret.fold_with(folder);
        VariantDef::new(fields, ret)
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.fields.iter().for_each(|ty| ty.visit_with(visitor));
        self.ret.visit_with(visitor);
    }
}

impl<T: TypeFoldable> TypeFoldable for Opaqueness<T> {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        self.as_ref().map(|t| t.fold_with(folder))
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        if let Opaqueness::Transparent(t) = self {
            t.visit_with(visitor);
        }
    }
}

impl TypeFoldable for FnSig {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        let requires = self.requires.fold_with(folder);
        let args = self.args.fold_with(folder);
        let output = self.output.fold_with(folder);
        FnSig::new(requires, args, output)
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.requires
            .iter()
            .for_each(|constr| constr.visit_with(visitor));
        self.args.iter().for_each(|arg| arg.visit_with(visitor));
        self.output.visit_with(visitor);
    }
}

impl TypeFoldable for FnOutput {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        FnOutput::new(self.ret.fold_with(folder), self.ensures.fold_with(folder))
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.ret.visit_with(visitor);
        self.ensures.visit_with(visitor);
    }
}

impl TypeFoldable for Constraint {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            Constraint::Type(path, ty) => {
                let path_expr = path
                    .to_expr()
                    .fold_with(folder)
                    .normalize(&Default::default());
                Constraint::Type(
                    path_expr.to_path().unwrap_or_else(|| {
                        bug!("invalid path `{path_expr:?}` produced when folding `{self:?}`",)
                    }),
                    ty.fold_with(folder),
                )
            }
            Constraint::Pred(e) => Constraint::Pred(e.fold_with(folder)),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self {
            Constraint::Type(path, ty) => {
                path.to_expr().visit_with(visitor);
                ty.visit_with(visitor);
            }
            Constraint::Pred(e) => e.visit_with(visitor),
        }
    }
}

impl TypeFoldable for Ty {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Ty {
        match self.kind() {
            TyKind::Indexed(bty, idxs) => {
                Ty::indexed(bty.fold_with(folder), idxs.fold_with(folder))
            }
            TyKind::Exists(exists) => TyKind::Exists(exists.fold_with(folder)).intern(),
            TyKind::Ptr(pk, path) => {
                Ty::ptr(
                    *pk,
                    path.to_expr()
                        .fold_with(folder)
                        .normalize(&Default::default())
                        .to_path()
                        .expect("folding produced an invalid path"),
                )
            }
            TyKind::Constr(pred, ty) => Ty::constr(pred.fold_with(folder), ty.fold_with(folder)),
            TyKind::Param(_) | TyKind::Uninit | TyKind::Discr(..) => self.clone(),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self.kind() {
            TyKind::Indexed(bty, idxs) => {
                bty.visit_with(visitor);
                idxs.visit_with(visitor);
            }
            TyKind::Exists(exists) => {
                exists.visit_with(visitor);
            }
            TyKind::Ptr(_, path) => path.to_expr().visit_with(visitor),
            TyKind::Constr(pred, ty) => {
                pred.visit_with(visitor);
                ty.visit_with(visitor);
            }
            TyKind::Param(_) | TyKind::Discr(..) | TyKind::Uninit => {}
        }
    }

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        folder.fold_ty(self)
    }

    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        visitor.visit_ty(self);
    }
}

impl TypeFoldable for Index {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        Index { expr: self.expr.fold_with(folder), is_binder: self.is_binder.clone() }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.expr.visit_with(visitor);
    }
}

impl TypeFoldable for BaseTy {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            BaseTy::Adt(adt_def, substs) => BaseTy::adt(adt_def.clone(), substs.fold_with(folder)),
            BaseTy::Slice(ty) => BaseTy::Slice(ty.fold_with(folder)),
            BaseTy::RawPtr(ty, mu) => BaseTy::RawPtr(ty.fold_with(folder), *mu),
            BaseTy::Ref(rk, ty) => BaseTy::Ref(*rk, ty.fold_with(folder)),
            BaseTy::Tuple(tys) => BaseTy::Tuple(tys.fold_with(folder)),
            BaseTy::Array(ty, c) => BaseTy::Array(ty.fold_with(folder), c.clone()),
            BaseTy::Int(_)
            | BaseTy::Param(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::Never => self.clone(),
            BaseTy::Closure(did) => BaseTy::Closure(*did),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self {
            BaseTy::Adt(_, substs) => substs.iter().for_each(|ty| ty.visit_with(visitor)),
            BaseTy::Slice(ty) => ty.visit_with(visitor),
            BaseTy::RawPtr(ty, _) => ty.visit_with(visitor),
            BaseTy::Ref(_, ty) => ty.visit_with(visitor),
            BaseTy::Tuple(tys) => tys.iter().for_each(|ty| ty.visit_with(visitor)),
            BaseTy::Array(ty, _) => ty.visit_with(visitor),
            BaseTy::Int(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::Closure(_)
            | BaseTy::Never
            | BaseTy::Param(_) => {}
        }
    }

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        folder.fold_bty(self)
    }

    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        visitor.visit_bty(self);
    }
}

impl TypeFoldable for GenericArg {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            GenericArg::Ty(ty) => GenericArg::Ty(ty.fold_with(folder)),
            GenericArg::BaseTy(ty) => GenericArg::BaseTy(ty.fold_with(folder)),
            GenericArg::Lifetime => GenericArg::Lifetime,
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self {
            GenericArg::Ty(ty) => ty.visit_with(visitor),
            GenericArg::BaseTy(ty) => ty.visit_with(visitor),
            GenericArg::Lifetime => {}
        }
    }
}

impl TypeFoldable for KVar {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        KVar { kvid: self.kvid, self_args: self.self_args, args: self.args.fold_with(folder) }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.args.visit_with(visitor);
    }
}

impl TypeFoldable for Expr {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self.kind() {
            ExprKind::Var(var) => Expr::var(*var),
            ExprKind::Local(local) => Expr::local(*local),
            ExprKind::Constant(c) => Expr::constant(*c),
            ExprKind::ConstDefId(did) => Expr::const_def_id(*did),
            ExprKind::BinaryOp(op, e1, e2) => {
                Expr::binary_op(*op, e1.fold_with(folder), e2.fold_with(folder))
            }
            ExprKind::UnaryOp(op, e) => Expr::unary_op(*op, e.fold_with(folder)),
            ExprKind::TupleProj(e, proj) => Expr::tuple_proj(e.fold_with(folder), *proj),
            ExprKind::Tuple(exprs) => {
                Expr::tuple(exprs.iter().map(|e| e.fold_with(folder)).collect_vec())
            }
            ExprKind::PathProj(e, field) => Expr::path_proj(e.fold_with(folder), *field),
            ExprKind::App(func, arg) => Expr::app(func.fold_with(folder), arg.fold_with(folder)),
            ExprKind::IfThenElse(p, e1, e2) => {
                Expr::ite(p.fold_with(folder), e1.fold_with(folder), e2.fold_with(folder))
            }
            ExprKind::Hole => Expr::hole(),
            ExprKind::KVar(kvar) => Expr::kvar(kvar.fold_with(folder)),
            ExprKind::Abs(body) => Expr::abs(body.fold_with(folder)),
            ExprKind::Func(func) => Expr::func(*func),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self.kind() {
            ExprKind::Var(Var::Free(name)) => visitor.visit_fvar(*name),
            ExprKind::BinaryOp(_, e1, e2) => {
                e1.visit_with(visitor);
                e2.visit_with(visitor);
            }
            ExprKind::Tuple(exprs) => {
                for e in exprs {
                    e.visit_with(visitor);
                }
            }
            ExprKind::PathProj(e, _) | ExprKind::UnaryOp(_, e) | ExprKind::TupleProj(e, _) => {
                e.visit_with(visitor);
            }
            ExprKind::App(func, arg) => {
                func.visit_with(visitor);
                arg.visit_with(visitor);
            }
            ExprKind::IfThenElse(p, e1, e2) => {
                p.visit_with(visitor);
                e1.visit_with(visitor);
                e2.visit_with(visitor);
            }
            ExprKind::KVar(kvar) => kvar.visit_with(visitor),
            ExprKind::Abs(body) => body.visit_with(visitor),
            ExprKind::Constant(_)
            | ExprKind::Hole
            | ExprKind::Var(_)
            | ExprKind::Local(_)
            | ExprKind::Func(_)
            | ExprKind::ConstDefId(_) => {}
        }
    }

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        folder.fold_expr(self)
    }

    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        visitor.visit_expr(self);
    }
}

impl<T> TypeFoldable for List<T>
where
    T: TypeFoldable,
    [T]: Internable,
{
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        List::from_iter(self.iter().map(|t| t.fold_with(folder)))
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.iter().for_each(|t| t.visit_with(visitor));
    }
}

impl TypeFoldable for Qualifier {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        Qualifier {
            name: self.name.clone(),
            body: self.body.fold_with(folder),
            global: self.global,
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.body.visit_with(visitor);
    }
}

impl TypeFoldable for Invariant {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        let pred = self.pred.fold_with(folder);
        Invariant { pred }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.pred.visit_with(visitor);
    }
}
