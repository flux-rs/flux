use std::iter;

use flux_middle::{
    global_env::{GlobalEnv, OpaqueStructErr, Variance},
    intern::List,
    rty::{
        evars::{self, EVarSol},
        fold::TypeFoldable,
        BaseTy, BinOp, Binders, Constraint, Constraints, EVarGen, Expr, ExprKind, GenericArg,
        PolySig, PolyVariant, Pred, RefKind, RefineArg, RefineArgs, Sort, Ty, TyKind, Var,
        VariantRet,
    },
    rustc::mir::BasicBlock,
};
use itertools::{izip, Itertools};
use rustc_span::Span;

use crate::{
    checker::errors::CheckerError,
    param_infer::InferenceError,
    refine_tree::{RefineCtxt, Scope, UnpackFlags},
    type_env::{PathMap, TypeEnv},
};

#[allow(clippy::type_complexity)]
pub struct ConstrGen<'a, 'tcx> {
    pub genv: &'a GlobalEnv<'a, 'tcx>,
    fresh_kvar: Box<dyn FnMut(&[Sort]) -> Binders<Pred> + 'a>,
    tag: Tag,
}

struct InferCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    kvar_gen: &'a mut (dyn FnMut(&[Sort]) -> Binders<Pred> + 'a),
    evar_gen: EVarGen,
    tag: Tag,
    scope: Scope,
    locs_cx: evars::CtxtId,
    evars_cx: evars::CtxtId,
}

pub struct CallOutput {
    pub ret: Ty,
    pub ensures: Constraints,
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub enum Tag {
    Call(Span),
    Assign(Span),
    Ret,
    RetAt(Span),
    Fold(Span),
    Assert(&'static str, Span),
    Div(Span),
    Rem(Span),
    Goto(Option<Span>, BasicBlock),
    Overflow(Span),
    Other,
}

impl Tag {
    pub fn span(&self) -> Option<Span> {
        match *self {
            Tag::Call(span)
            | Tag::Assign(span)
            | Tag::RetAt(span)
            | Tag::Fold(span)
            | Tag::Assert(_, span)
            | Tag::Div(span)
            | Tag::Rem(span)
            | Tag::Goto(Some(span), _) => Some(span),
            _ => None,
        }
    }
}

impl<'a, 'tcx> ConstrGen<'a, 'tcx> {
    pub fn new<F>(genv: &'a GlobalEnv<'a, 'tcx>, fresh_kvar: F, tag: Tag) -> Self
    where
        F: FnMut(&[Sort]) -> Binders<Pred> + 'a,
    {
        ConstrGen { genv, fresh_kvar: Box::new(fresh_kvar), tag }
    }

    pub fn check_constraint(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        constraint: &Constraint,
    ) -> Result<(), OpaqueStructErr> {
        self.infcx(rcx).check_constraint(rcx, env, constraint)
    }

    pub fn check_pred(&self, rcx: &mut RefineCtxt, pred: impl Into<Pred>) {
        rcx.check_pred(pred, self.tag);
    }

    pub fn subtyping(&mut self, rcx: &mut RefineCtxt, ty1: &Ty, ty2: &Ty) {
        self.infcx(rcx).subtyping(rcx, ty1, ty2)
    }

    pub fn check_fn_call(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        fn_sig: &PolySig,
        substs: &[GenericArg],
        actuals: &[Ty],
    ) -> Result<CallOutput, CheckerError> {
        // HACK(nilehmann) This let us infer parameters under mutable references for the simple case
        // where the formal argument is of the form `&mut B[@n]`, e.g., the type of the first argument
        // to `RVec::get_mut` is `&mut RVec<T>[@n]`. We should remove this after we implement opening of
        // mutable references.
        let actuals = iter::zip(actuals, fn_sig.as_ref().skip_binders().args())
            .map(|(actual, formal)| {
                if let (TyKind::Ref(RefKind::Mut, _), TyKind::Ref(RefKind::Mut, ty)) = (actual.kind(), formal.kind())
                   && let TyKind::Indexed(..) = ty.kind() {
                    rcx.unpack_with(actual, UnpackFlags::EXISTS_IN_MUT_REF)
                } else {
                    actual.clone()
                }
            })
            .collect_vec();

        // Replace holes with fresh kvars in generic arguments
        let substs = substs
            .iter()
            .map(|arg| arg.replace_holes(&mut self.fresh_kvar))
            .collect_vec();

        let mut infcx = self.infcx(rcx);

        // Generate fresh evars and kvars for refinement parameters
        let fn_sig = fn_sig
            .replace_generic_args(&substs)
            .replace_bvars_with(|sort| infcx.fresh_evar_or_kvar(sort));

        // Check arguments
        for (actual, formal) in iter::zip(&actuals, fn_sig.args()) {
            let (formal, pred) = formal.unconstr();
            infcx.check_pred(rcx, pred);
            match (actual.kind(), formal.kind()) {
                (TyKind::Ptr(RefKind::Mut, path), TyKind::Ref(RefKind::Mut, bound)) => {
                    infcx.subtyping(rcx, &env.get(path), bound);
                    env.update(path, bound.clone());
                    env.block(path);
                }
                (TyKind::Ptr(RefKind::Shr, path), TyKind::Ref(RefKind::Shr, bound)) => {
                    infcx.subtyping(rcx, &env.get(path), bound);
                    env.block(path);
                }
                _ => infcx.subtyping(rcx, actual, &formal),
            }
        }

        // Check preconditions
        let locs_sol = infcx.solve_locs();
        for constraint in &fn_sig.requires().replace_evars(&locs_sol) {
            infcx.check_constraint(rcx, env, constraint)?;
        }

        // Replace evars
        let mut evars_sol = infcx.solve();
        evars_sol.extend(locs_sol);

        env.replace_evars(&evars_sol);
        rcx.replace_evars(&evars_sol);
        let ret = fn_sig.ret().replace_evars(&evars_sol);
        let ensures = fn_sig.ensures().replace_evars(&evars_sol);

        Ok(CallOutput { ret, ensures })
    }

    pub fn check_constructor(
        &mut self,
        rcx: &mut RefineCtxt,
        variant: &PolyVariant,
        substs: &[GenericArg],
        fields: &[Ty],
    ) -> Result<VariantRet, InferenceError> {
        // Generate fresh kvars for generic types
        let substs = substs
            .iter()
            .map(|arg| arg.replace_holes(&mut self.fresh_kvar))
            .collect_vec();

        let mut infcx = self.infcx(rcx);
        let variant = variant
            .replace_generic_args(&substs)
            .replace_bvars_with(|sort| infcx.fresh_evar_or_kvar(sort));

        // Check arguments
        for (actual, formal) in iter::zip(fields, variant.fields()) {
            infcx.subtyping(rcx, actual, formal);
        }

        let evars_sol = infcx.solve();
        rcx.replace_evars(&evars_sol);

        Ok(variant.ret.replace_evars(&evars_sol))
    }

    fn infcx(&mut self, rcx: &RefineCtxt) -> InferCtxt<'_, 'tcx> {
        InferCtxt::new(self.genv, rcx, &mut self.fresh_kvar, self.tag)
    }
}

impl<'a, 'tcx> InferCtxt<'a, 'tcx> {
    fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        rcx: &RefineCtxt,
        kvar_gen: &'a mut (dyn FnMut(&[Sort]) -> Binders<Pred> + 'a),
        tag: Tag,
    ) -> Self {
        let mut evar_gen = EVarGen::new();
        let scope = rcx.scope();
        let locs_cx = evar_gen.new_ctxt();
        let evars_cx = evar_gen.new_ctxt();
        Self { genv, kvar_gen, scope, evar_gen, locs_cx, evars_cx, tag }
    }

    fn fresh_evar_or_kvar(&mut self, sort: &Sort) -> RefineArg {
        match sort {
            Sort::Func(fsort) if fsort.output().is_bool() => {
                RefineArg::Abs((self.kvar_gen)(fsort.inputs()))
            }
            Sort::Loc => {
                let evar = self.evar_gen.fresh_in_cx(self.locs_cx);
                RefineArg::Expr(Expr::evar(evar))
            }
            _ => {
                let evar = self.evar_gen.fresh_in_cx(self.evars_cx);
                RefineArg::Expr(Expr::evar(evar))
            }
        }
    }

    fn check_pred(&self, rcx: &mut RefineCtxt, pred: impl Into<Pred>) {
        rcx.check_pred(pred, self.tag)
    }

    fn check_constraint(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        constraint: &Constraint,
    ) -> Result<(), OpaqueStructErr> {
        let rcx = &mut rcx.breadcrumb();
        match constraint {
            Constraint::Type(path, ty) => {
                let actual_ty = {
                    let gen = &mut ConstrGen::new(self.genv, &mut *self.kvar_gen, self.tag);
                    env.lookup_path(rcx, gen, path)?
                };
                self.subtyping(rcx, &actual_ty, ty);
            }
            Constraint::Pred(e) => {
                rcx.check_pred(e, self.tag);
            }
        }
        Ok(())
    }

    fn subtyping(&mut self, rcx: &mut RefineCtxt, ty1: &Ty, ty2: &Ty) {
        let rcx = &mut rcx.breadcrumb();
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Exists(bty1, p1), TyKind::Exists(bty2, p2)) if p1 == p2 => {
                self.bty_subtyping(rcx, bty1, bty2);
                return;
            }
            (TyKind::Exists(bty, pred), _) => {
                let idxs = rcx.assume_bound_pred(pred);
                let ty1 = Ty::indexed(bty.clone(), RefineArgs::multi(idxs));
                self.subtyping(rcx, &ty1, ty2);
                return;
            }
            _ => {}
        }

        match (ty1.kind(), ty2.kind()) {
            (TyKind::Indexed(bty1, idxs1), TyKind::Indexed(bty2, idxs2)) => {
                self.bty_subtyping(rcx, bty1, bty2);
                for (i, (arg1, arg2)) in iter::zip(idxs1.args(), idxs2.args()).enumerate() {
                    self.arg_subtyping(rcx, arg1, arg2, idxs2.is_binder(i));
                }
            }
            (TyKind::Indexed(bty1, idxs), TyKind::Exists(bty2, pred)) => {
                self.bty_subtyping(rcx, bty1, bty2);
                rcx.check_pred(pred.replace_bvars(idxs.args()), self.tag);
            }
            (TyKind::Ptr(rk1, path1), TyKind::Ptr(rk2, path2)) => {
                debug_assert_eq!(rk1, rk2);
                self.unify_exprs(&path1.to_expr(), &path2.to_expr(), false)
            }
            (TyKind::BoxPtr(loc1, alloc1), TyKind::BoxPtr(loc2, alloc2)) => {
                debug_assert_eq!(loc1, loc2);
                debug_assert_eq!(alloc1, alloc2);
            }
            (TyKind::Ref(RefKind::Mut, ty1), TyKind::Ref(RefKind::Mut, ty2)) => {
                self.subtyping(rcx, ty1, ty2);
                self.subtyping(rcx, ty2, ty1);
            }
            (TyKind::Ref(RefKind::Shr, ty1), TyKind::Ref(RefKind::Shr, ty2)) => {
                self.subtyping(rcx, ty1, ty2);
            }
            (_, TyKind::Uninit) => {
                // FIXME: we should rethink in which situation this is sound.
            }
            (TyKind::Param(param1), TyKind::Param(param2)) => {
                debug_assert_eq!(param1, param2);
            }
            (TyKind::Tuple(tys1), TyKind::Tuple(tys2)) => {
                debug_assert_eq!(tys1.len(), tys2.len());
                for (ty1, ty2) in iter::zip(tys1, tys2) {
                    self.subtyping(rcx, ty1, ty2);
                }
            }
            (_, TyKind::Constr(p2, ty2)) => {
                rcx.check_pred(p2, self.tag);
                self.subtyping(rcx, ty1, ty2);
            }
            (TyKind::Constr(p1, ty1), _) => {
                rcx.assume_pred(p1);
                self.subtyping(rcx, ty1, ty2);
            }
            _ => unreachable!("`{ty1:?}` <: `{ty2:?}`"),
        }
    }

    fn arg_subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        arg1: &RefineArg,
        arg2: &RefineArg,
        is_binder: bool,
    ) {
        if arg1 == arg2 {
            return;
        }
        match (arg1, arg2) {
            (RefineArg::Expr(e1), RefineArg::Expr(e2)) => {
                self.unify_exprs(e1, e2, is_binder);
                rcx.check_pred(Expr::binary_op(BinOp::Eq, e1, e2), self.tag);
            }
            (RefineArg::Abs(abs1), RefineArg::Abs(abs2)) => {
                debug_assert_eq!(abs1.params(), abs2.params());
                let args = rcx
                    .define_vars(abs1.params())
                    .into_iter()
                    .map(|var| RefineArg::Expr(var.into()))
                    .collect_vec();
                let pred1 = abs1.replace_bvars(&args);
                let pred2 = abs2.replace_bvars(&args);
                rcx.check_impl(&pred1, &pred2, self.tag);
                rcx.check_impl(pred2, pred1, self.tag);
            }
            (RefineArg::Expr(expr), RefineArg::Abs(abs))
            | (RefineArg::Abs(abs), RefineArg::Expr(expr)) => {
                if let ExprKind::FreeVar(name) = expr.kind() {
                    let args = rcx
                        .define_vars(abs.params())
                        .into_iter()
                        .map(Expr::from)
                        .collect_vec();
                    let pred1 = Pred::App(Var::Free(*name), List::from(&args[..]));
                    let args = args.into_iter().map(RefineArg::from).collect_vec();
                    let pred2 = abs.replace_bvars(&args);
                    rcx.check_impl(&pred1, &pred2, self.tag);
                    rcx.check_impl(pred2, pred1, self.tag);
                } else {
                    unreachable!("invalid refinement argument subtyping `{arg1:?}` - `{arg2:?}`")
                }
            }
        }
    }

    fn bty_subtyping(&mut self, rcx: &mut RefineCtxt, bty1: &BaseTy, bty2: &BaseTy) {
        match (bty1, bty2) {
            (BaseTy::Int(int_ty1), BaseTy::Int(int_ty2)) => {
                debug_assert_eq!(int_ty1, int_ty2);
            }
            (BaseTy::Uint(uint_ty1), BaseTy::Uint(uint_ty2)) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
            }
            (BaseTy::Adt(def1, substs1), BaseTy::Adt(def2, substs2)) => {
                debug_assert_eq!(def1.def_id(), def2.def_id());
                debug_assert_eq!(substs1.len(), substs2.len());
                let variances = self.genv.variances_of(def1.def_id());
                for (variance, ty1, ty2) in izip!(variances, substs1.iter(), substs2.iter()) {
                    self.generic_arg_subtyping(rcx, *variance, ty1, ty2);
                }
            }
            (BaseTy::Float(float_ty1), BaseTy::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
            }
            (BaseTy::Array(ty1, len1), BaseTy::Array(ty2, len2)) => {
                debug_assert_eq!(len1, len2);
                self.subtyping(rcx, ty1, ty2);
            }
            (BaseTy::Slice(ty1), BaseTy::Slice(ty2)) => {
                self.subtyping(rcx, ty1, ty2);
            }
            (BaseTy::Bool, BaseTy::Bool)
            | (BaseTy::Str, BaseTy::Str)
            | (BaseTy::Char, BaseTy::Char) => {}
            _ => {
                unreachable!(
                    "unexpected base types: `{:?}` and `{:?}` at {:?}",
                    bty1,
                    bty2,
                    self.tag.span()
                )
            }
        }
    }

    fn generic_arg_subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        variance: Variance,
        arg1: &GenericArg,
        arg2: &GenericArg,
    ) {
        match (arg1, arg2) {
            (GenericArg::Ty(ty1), GenericArg::Ty(ty2)) => {
                match variance {
                    rustc_middle::ty::Variance::Covariant => self.subtyping(rcx, ty1, ty2),
                    rustc_middle::ty::Variance::Invariant => {
                        self.subtyping(rcx, ty1, ty2);
                        self.subtyping(rcx, ty2, ty1);
                    }
                    rustc_middle::ty::Variance::Contravariant => self.subtyping(rcx, ty2, ty1),
                    rustc_middle::ty::Variance::Bivariant => {}
                }
            }
            (GenericArg::Lifetime, GenericArg::Lifetime) => {}
            _ => unreachable!("incompatible generic args:  `{arg1:?}` `{arg2:?}"),
        };
    }

    fn unify_exprs(&mut self, e1: &Expr, e2: &Expr, replace: bool) {
        if let ExprKind::EVar(evar) = e2.kind()
           && !self.scope.has_free_vars(e1)
        {
            self.evar_gen.unify(*evar, e1, replace);
        }
    }

    fn solve(mut self) -> EVarSol {
        self.evar_gen.solve(self.evars_cx).unwrap()
    }

    fn solve_locs(&mut self) -> EVarSol {
        self.evar_gen.solve(self.locs_cx).unwrap()
    }
}

mod pretty {
    use std::fmt;

    use flux_middle::pretty::*;

    use super::*;

    impl Pretty for Tag {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Tag::Call(span) => w!("Call({:?})", span),
                Tag::Assign(span) => w!("Assign({:?})", span),
                Tag::Ret => w!("Ret"),
                Tag::RetAt(span) => w!("RetAt({:?})", span),
                Tag::Div(span) => w!("Div({:?})", span),
                Tag::Rem(span) => w!("Rem({:?})", span),
                Tag::Goto(span, bb) => {
                    if let Some(span) = span {
                        w!("Goto({:?}, {:?})", span, ^bb)
                    } else {
                        w!("Goto({:?})", ^bb)
                    }
                }
                Tag::Assert(msg, span) => w!("Assert(\"{}\", {:?})", ^msg, span),
                Tag::Fold(span) => w!("Fold({:?})", span),
                Tag::Other => w!("Other"),
                Tag::Overflow(span) => w!("Overflow({:?})", span),
            }
        }
    }

    impl_debug_with_default_cx!(Tag);
}
