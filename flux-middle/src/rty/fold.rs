//! This modules folows the implementation of folding in rustc. For more information read the
//! documentation in [`rustc_middle::ty::fold`].

use itertools::Itertools;
use rustc_hash::FxHashSet;

use super::{
    evars::EVarSol, AdtDef, AdtDefData, BaseTy, Binders, Constraint, Defns, Expr, ExprKind, FnSig,
    GenericArg, Invariant, KVar, Name, PolySig, Qualifier, RefineArg, RefineArgs, RefineArgsData,
    Sort, Ty, TyKind, VariantRet,
};
use crate::{
    intern::{Internable, Interned, List},
    rty::{Func, Var, VariantDef},
};

pub trait TypeVisitor: Sized {
    fn visit_fvar(&mut self, name: Name) {
        name.super_visit_with(self);
    }
}

pub trait TypeFolder: Sized {
    fn fold_binders<T: TypeFoldable>(&mut self, t: &Binders<T>) -> Binders<T> {
        t.super_fold_with(self)
    }

    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        ty.super_fold_with(self)
    }

    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        expr.super_fold_with(self)
    }

    fn fold_refine_arg(&mut self, arg: &RefineArg) -> RefineArg {
        arg.super_fold_with(self)
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

    fn normalize(&self, defns: &Defns) -> Self {
        struct Normalize<'a>(&'a Defns);

        impl<'a> TypeFolder for Normalize<'a> {
            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::App(func, args) = expr.kind()
                   && let Func::Uif(sym) = func
                {
                    let exp_args: List<Expr> =
                        args.iter().map(|arg| arg.super_fold_with(self)).collect();
                    self.0.app(sym, exp_args)
                } else {
                    expr.super_fold_with(self)
                }
            }
        }
        self.fold_with(&mut Normalize(defns))
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

    /// Replaces all [`holes`] with a fresh [`predicate`] generated by calling `mk_pred`.
    ///
    /// [`holes`]: Pred::Hole
    /// [`predicate`]: Pred
    fn replace_holes(&self, mk_pred: &mut impl FnMut(&[Sort]) -> Binders<Expr>) -> Self {
        struct ReplaceHoles<'a, F>(&'a mut F, &'a [Sort]);

        impl<'a, F> TypeFolder for ReplaceHoles<'a, F>
        where
            F: FnMut(&[Sort]) -> Binders<Expr>,
        {
            fn fold_binders<T: TypeFoldable>(&mut self, t: &Binders<T>) -> Binders<T> {
                t.super_fold_with(&mut ReplaceHoles(&mut self.0, &t.params))
            }

            fn fold_expr(&mut self, e: &Expr) -> Expr {
                if let ExprKind::Hole = e.kind() {
                    let binders = self.0(self.1);
                    debug_assert_eq!(&binders.params[..], self.1);
                    binders.skip_binders()
                } else {
                    e.super_fold_with(self)
                }
            }
        }

        self.fold_with(&mut ReplaceHoles(mk_pred, &[]))
    }

    /// Turns each [`TyKind::Indexed`] into [`TyKind::Exists`] with a [`hole`] and replaces
    /// all existing [`predicates`] with a [`hole`].
    /// For example, `Vec<i32{v: v > 0}>[n]` becomes `Vec<i32{v: *}>{v: *}`.
    ///
    /// [`hole`]: Pred::Hole
    /// [`predicates`]: Pred
    fn with_holes(&self) -> Self {
        struct WithHoles;

        impl TypeFolder for WithHoles {
            fn fold_ty(&mut self, ty: &Ty) -> Ty {
                if let TyKind::Indexed(bty, _) | TyKind::Exists(bty, _) = ty.kind() {
                    let sorts = bty.sorts();
                    Ty::exists(bty.super_fold_with(self), Binders::new(Expr::hole(), sorts))
                } else {
                    ty.super_fold_with(self)
                }
            }
        }

        self.fold_with(&mut WithHoles)
    }

    fn replace_generic_args(&self, args: &[GenericArg]) -> Self {
        struct GenericsFolder<'a>(&'a [GenericArg]);

        impl TypeFolder for GenericsFolder<'_> {
            fn fold_ty(&mut self, ty: &Ty) -> Ty {
                if let TyKind::Param(param_ty) = ty.kind() {
                    match &self.0[param_ty.index as usize] {
                        GenericArg::Ty(ty) => ty.clone(),
                        GenericArg::Lifetime => {
                            unreachable!("invalid generic argument")
                        }
                    }
                } else {
                    ty.super_fold_with(self)
                }
            }
        }

        self.fold_with(&mut GenericsFolder(args))
    }

    fn replace_evars(&self, evars: &EVarSol) -> Self {
        struct EVarFolder<'a>(&'a EVarSol);

        impl TypeFolder for EVarFolder<'_> {
            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::EVar(evar) = expr.kind()
                   && let Some(sol) = self.0.get(*evar)
                {
                    if let RefineArg::Expr(e) = sol {
                        e.clone()
                    } else {
                        panic!("expected expr for `{expr:?}` but found `{:?}` when substituting", sol)
                    }
                } else if let ExprKind::App(Func::Var(Var::EVar(evar)), args) = expr.kind()
                    && let Some(sol) = self.0.get(*evar)
                    && let RefineArg::Abs(abs) = sol
                {
                    let args = args.iter().map(|arg| RefineArg::Expr(arg.fold_with(self))).collect_vec();
                    abs.replace_bvars(&args)
                } else {
                    expr.super_fold_with(self)
                }
            }
        }

        self.fold_with(&mut EVarFolder(evars))
    }
}

impl<T> TypeFoldable for Binders<T>
where
    T: TypeFoldable,
{
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        Binders::new(self.value.fold_with(folder), self.params.clone())
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.value.visit_with(visitor);
    }

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        folder.fold_binders(self)
    }
}

impl TypeFoldable for PolySig {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        PolySig::new(self.fn_sig.fold_with(folder), &self.modes[..])
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

impl TypeFoldable for VariantRet {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        let bty = self.bty.fold_with(folder);
        let args = self.args.fold_with(folder);
        VariantRet { bty, args }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.bty.visit_with(visitor);
        self.args.iter().for_each(|idx| idx.visit_with(visitor));
    }
}

impl TypeFoldable for FnSig {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        let requires = self.requires.fold_with(folder);
        let args = self.args.fold_with(folder);
        let ensures = self.ensures.fold_with(folder);
        let ret = self.ret.fold_with(folder);
        FnSig::new(requires, args, ret, ensures)
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.requires
            .iter()
            .for_each(|constr| constr.visit_with(visitor));
        self.args.iter().for_each(|arg| arg.visit_with(visitor));
        self.ensures
            .iter()
            .for_each(|constr| constr.visit_with(visitor));
        self.ret.visit_with(visitor);
    }
}

impl TypeFoldable for Constraint {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            Constraint::Type(path, ty) => {
                let path_expr = path.to_expr().fold_with(folder);
                Constraint::Type(
                    path_expr.to_path().unwrap_or_else(|| {
                        panic!("invalid path `{path_expr:?}` produced when folding `{self:?}`",)
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
            TyKind::Exists(bty, pred) => {
                TyKind::Exists(bty.fold_with(folder), pred.fold_with(folder)).intern()
            }
            TyKind::Tuple(tys) => Ty::tuple(tys.fold_with(folder)),
            TyKind::Array(ty, c) => Ty::array(ty.fold_with(folder), c.clone()),
            TyKind::Ptr(rk, path) => {
                Ty::ptr(
                    *rk,
                    path.to_expr()
                        .fold_with(folder)
                        .to_path()
                        .expect("folding produced an invalid path"),
                )
            }
            TyKind::BoxPtr(loc, alloc) => {
                Ty::box_ptr(
                    Expr::fvar(*loc)
                        .fold_with(folder)
                        .to_name()
                        .expect("folding produced an invalid name"),
                    alloc.fold_with(folder),
                )
            }
            TyKind::Ref(rk, ty) => Ty::mk_ref(*rk, ty.fold_with(folder)),
            TyKind::Constr(pred, ty) => Ty::constr(pred.fold_with(folder), ty.fold_with(folder)),
            TyKind::Uninit | TyKind::Param(_) | TyKind::Never | TyKind::Discr(..) => self.clone(),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self.kind() {
            TyKind::Indexed(bty, idxs) => {
                bty.visit_with(visitor);
                idxs.visit_with(visitor);
            }
            TyKind::Exists(bty, pred) => {
                bty.visit_with(visitor);
                pred.visit_with(visitor);
            }
            TyKind::Tuple(tys) => tys.iter().for_each(|ty| ty.visit_with(visitor)),
            TyKind::Array(ty, _) => ty.visit_with(visitor),
            TyKind::Ref(_, ty) => ty.visit_with(visitor),
            TyKind::Ptr(_, path) => path.to_expr().visit_with(visitor),
            TyKind::BoxPtr(loc, ty) => {
                Expr::fvar(*loc).visit_with(visitor);
                ty.visit_with(visitor);
            }
            TyKind::Constr(pred, ty) => {
                pred.visit_with(visitor);
                ty.visit_with(visitor);
            }
            TyKind::Param(_) | TyKind::Never | TyKind::Discr(..) | TyKind::Uninit => {}
        }
    }

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        folder.fold_ty(self)
    }
}

impl TypeFoldable for RefineArgs {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        RefineArgsData {
            args: self
                .0
                .args
                .iter()
                .map(|arg| arg.fold_with(folder))
                .collect_vec(),
            is_binder: self.0.is_binder.clone(),
        }
        .intern()
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.args().iter().for_each(|arg| arg.visit_with(visitor));
    }
}

impl TypeFoldable for RefineArg {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            RefineArg::Expr(e) => RefineArg::Expr(e.fold_with(folder)),
            RefineArg::Abs(abs) => RefineArg::Abs(abs.fold_with(folder)),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self {
            RefineArg::Expr(e) => e.visit_with(visitor),
            RefineArg::Abs(kvar) => kvar.visit_with(visitor),
        }
    }

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        folder.fold_refine_arg(self)
    }
}

impl TypeFoldable for BaseTy {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            BaseTy::Adt(adt_def, substs) => BaseTy::adt(adt_def.clone(), substs.fold_with(folder)),
            BaseTy::Slice(ty) => BaseTy::Slice(ty.fold_with(folder)),
            BaseTy::Int(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char => self.clone(),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self {
            BaseTy::Adt(_, substs) => substs.iter().for_each(|ty| ty.visit_with(visitor)),
            BaseTy::Slice(ty) => ty.visit_with(visitor),
            BaseTy::Int(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char => {}
        }
    }
}

impl TypeFoldable for GenericArg {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            GenericArg::Ty(ty) => GenericArg::Ty(ty.fold_with(folder)),
            GenericArg::Lifetime => GenericArg::Lifetime,
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self {
            GenericArg::Ty(ty) => ty.visit_with(visitor),
            GenericArg::Lifetime => {}
        }
    }
}

impl TypeFoldable for KVar {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        let KVar { kvid, args, scope } = self;
        let args = args.iter().map(|e| e.fold_with(folder)).collect();
        let scope = scope.iter().map(|e| e.fold_with(folder)).collect();
        KVar::new(*kvid, args, scope)
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.args.iter().for_each(|e| e.visit_with(visitor));
    }
}

impl TypeFoldable for Expr {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self.kind() {
            ExprKind::FreeVar(name) => Expr::fvar(name.fold_with(folder)),
            ExprKind::BoundVar(bvar) => Expr::bvar(*bvar),
            ExprKind::EVar(evar) => Expr::evar(*evar),
            ExprKind::Local(local) => Expr::local(*local),
            ExprKind::Constant(c) => Expr::constant(*c),
            ExprKind::ConstDefId(did) => Expr::const_def_id(*did),
            ExprKind::BinaryOp(op, e1, e2) => {
                Expr::binary_op(*op, e1.fold_with(folder), e2.fold_with(folder))
            }
            ExprKind::UnaryOp(op, e) => Expr::unary_op(*op, e.fold_with(folder)),
            ExprKind::TupleProj(e, proj) => Expr::proj(e.fold_with(folder), *proj),
            ExprKind::Tuple(exprs) => {
                Expr::tuple(exprs.iter().map(|e| e.fold_with(folder)).collect_vec())
            }
            ExprKind::PathProj(e, field) => Expr::path_proj(e.fold_with(folder), *field),
            ExprKind::App(func, args) => Expr::app(func.fold_with(folder), args.fold_with(folder)),
            ExprKind::IfThenElse(p, e1, e2) => {
                Expr::ite(p.fold_with(folder), e1.fold_with(folder), e2.fold_with(folder))
            }
            ExprKind::Hole => Expr::hole(),
            ExprKind::KVar(kvar) => Expr::kvar(kvar.fold_with(folder)),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self.kind() {
            ExprKind::FreeVar(name) => name.visit_with(visitor),
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
            ExprKind::App(func, args) => {
                func.visit_with(visitor);
                for e in args {
                    e.visit_with(visitor);
                }
            }
            ExprKind::IfThenElse(p, e1, e2) => {
                p.visit_with(visitor);
                e1.visit_with(visitor);
                e2.visit_with(visitor);
            }
            ExprKind::KVar(kvar) => kvar.visit_with(visitor),
            ExprKind::Constant(_)
            | ExprKind::Hole
            | ExprKind::BoundVar(_)
            | ExprKind::EVar(_)
            | ExprKind::Local(_)
            | ExprKind::ConstDefId(_) => {}
        }
    }

    fn fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        folder.fold_expr(self)
    }
}

impl TypeFoldable for Func {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            Func::Var(var) => Func::Var(var.fold_with(folder)),
            Func::Uif(sym) => Func::Uif(*sym),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self {
            Func::Var(var) => var.visit_with(visitor),
            Func::Uif(_) => {}
        }
    }
}

impl TypeFoldable for Var {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        self.to_expr()
            .fold_with(folder)
            .to_var()
            .expect("folding produced invalid var")
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.to_expr().visit_with(visitor)
    }
}

impl TypeFoldable for Name {
    fn super_fold_with<F: TypeFolder>(&self, _folder: &mut F) -> Self {
        *self
    }

    fn super_visit_with<V: TypeVisitor>(&self, _visitor: &mut V) {}

    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        visitor.visit_fvar(*self);
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
            args: self.args.clone(),
            expr: self.expr.fold_with(folder),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.expr.visit_with(visitor)
    }
}

impl TypeFoldable for AdtDef {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        AdtDef(Interned::new(AdtDefData {
            def_id: self.def_id(),
            sorts: self.sorts().to_vec(),
            flags: *self.flags(),
            nvariants: self.0.nvariants,
            opaque: self.0.opaque,
            invariants: self
                .invariants()
                .iter()
                .map(|inv| inv.fold_with(folder))
                .collect_vec(),
        }))
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        self.invariants()
            .iter()
            .for_each(|inv| inv.visit_with(visitor));
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

impl VariantDef {
    pub fn new(fields: Vec<Ty>, ret: VariantRet) -> Self {
        VariantDef { fields: List::from_vec(fields), ret }
    }

    pub fn fields(&self) -> &[Ty] {
        &self.fields
    }
}
