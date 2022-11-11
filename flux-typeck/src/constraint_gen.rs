use std::iter;

use flux_middle::{
    global_env::{GlobalEnv, OpaqueStructErr, Variance},
    intern::List,
    rty::{
        fold::TypeFoldable, BaseTy, BinOp, Binders, Constraint, Constraints, Expr, ExprKind,
        GenericArg, PolySig, PolyVariant, Pred, RefKind, RefineArg, RefineArgs, Sort, Ty, TyKind,
        Var, VariantRet,
    },
    rustc::mir::BasicBlock,
};
use itertools::{izip, Itertools};
use rustc_span::Span;

use crate::{
    checker::errors::CheckerError,
    param_infer::{self, InferenceError},
    refine_tree::{ConstrBuilder, RefineCtxt, UnpackFlags},
    type_env::{PathMap, TypeEnv},
};

#[allow(clippy::type_complexity)]
pub struct ConstrGen<'a, 'tcx> {
    pub genv: &'a GlobalEnv<'a, 'tcx>,
    fresh_kvar: Box<dyn FnMut(&[Sort]) -> Binders<Pred> + 'a>,
    tag: Tag,
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
        match constraint {
            Constraint::Type(path, ty) => {
                let actual_ty = env.lookup_path(rcx, self, path)?;
                let mut constr = rcx.check_constr();
                subtyping(self.genv, &mut constr, &actual_ty, ty, self.tag);
            }
            Constraint::Pred(e) => {
                let constr = &mut rcx.check_constr();
                constr.push_head(e.clone(), self.tag);
            }
        }
        Ok(())
    }

    pub fn check_pred(&mut self, rcx: &mut RefineCtxt, pred: impl Into<Pred>) {
        let mut constr = rcx.check_constr();
        constr.push_head(pred, self.tag);
    }

    pub fn subtyping(&mut self, rcx: &mut RefineCtxt, ty1: &Ty, ty2: &Ty) {
        let mut constr = rcx.check_constr();
        subtyping(self.genv, &mut constr, ty1, ty2, self.tag);
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

        // Generate fresh kvars for generic types
        let substs = substs
            .iter()
            .map(|arg| arg.replace_holes(&mut self.fresh_kvar))
            .collect_vec();

        // Infer refinement parameters
        let exprs = param_infer::infer_from_fn_call(env, &actuals, fn_sig, &mut self.fresh_kvar)?;
        let fn_sig = fn_sig
            .replace_generic_args(&substs)
            .replace_bound_vars(&exprs);

        let constr = &mut rcx.check_constr();

        // Convert pointers to borrows
        let actuals = iter::zip(actuals, fn_sig.args())
            .map(|(actual, formal)| {
                let formal = formal.unconstr();
                match (actual.kind(), formal.kind()) {
                    (TyKind::Ptr(RefKind::Mut, path), TyKind::Ref(RefKind::Mut, bound)) => {
                        subtyping(self.genv, constr, &env.get(path), bound, self.tag);
                        env.update(path, bound.clone());
                        env.block(path);
                        Ty::mk_ref(RefKind::Mut, bound.clone())
                    }
                    (TyKind::Ptr(RefKind::Shr, path), TyKind::Ref(RefKind::Shr, _)) => {
                        let ty = Ty::mk_ref(RefKind::Shr, env.get(path));
                        env.block(path);
                        ty
                    }
                    _ => actual.clone(),
                }
            })
            .collect_vec();

        // Check arguments
        for (actual, formal) in iter::zip(actuals, fn_sig.args()) {
            subtyping(self.genv, constr, &actual, formal, self.tag);
        }

        // Check preconditions
        for constraint in fn_sig.requires() {
            self.check_constraint(rcx, env, constraint)?;
        }

        Ok(CallOutput { ret: fn_sig.ret().clone(), ensures: fn_sig.ensures().clone() })
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

        // Infer refinement parameters
        let exprs = param_infer::infer_from_constructor(fields, variant, &mut self.fresh_kvar)?;
        let variant = variant
            .replace_generic_args(&substs)
            .replace_bound_vars(&exprs);

        let constr = &mut rcx.check_constr();

        // Check arguments
        for (actual, formal) in iter::zip(fields, variant.fields()) {
            subtyping(self.genv, constr, actual, formal, self.tag);
        }

        Ok(variant.ret)
    }
}

fn subtyping(genv: &GlobalEnv, constr: &mut ConstrBuilder, ty1: &Ty, ty2: &Ty, tag: Tag) {
    let constr = &mut constr.breadcrumb();
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Exists(bty1, p1), TyKind::Exists(bty2, p2)) if p1 == p2 => {
            bty_subtyping(genv, constr, bty1, bty2, tag);
            return;
        }
        (TyKind::Exists(bty, pred), _) => {
            let idxs = constr.push_bound_guard(pred);
            let ty1 = Ty::indexed(bty.clone(), RefineArgs::multi(idxs));
            subtyping(genv, constr, &ty1, ty2, tag);
            return;
        }
        _ => {}
    }

    match (ty1.kind(), ty2.kind()) {
        (TyKind::Indexed(bty1, idxs1), TyKind::Indexed(bty2, idx2)) => {
            println!("{ty1:?} <: {ty2:?}");
            bty_subtyping(genv, constr, bty1, bty2, tag);
            for (arg1, arg2) in iter::zip(idxs1.args(), idx2.args()) {
                arg_subtyping(constr, arg1, arg2, tag);
            }
        }
        (TyKind::Indexed(bty1, idxs), TyKind::Exists(bty2, pred)) => {
            bty_subtyping(genv, constr, bty1, bty2, tag);
            constr.push_head(pred.replace_bound_vars(idxs.args()), tag);
        }
        (TyKind::Ptr(rk1, path1), TyKind::Ptr(rk2, path2)) => {
            debug_assert_eq!(rk1, rk2);
            debug_assert_eq!(path1, path2);
        }
        (TyKind::BoxPtr(loc1, alloc1), TyKind::BoxPtr(loc2, alloc2)) => {
            debug_assert_eq!(loc1, loc2);
            debug_assert_eq!(alloc1, alloc2);
        }
        (TyKind::Ref(RefKind::Mut, ty1), TyKind::Ref(RefKind::Mut, ty2)) => {
            subtyping(genv, constr, ty1, ty2, tag);
            subtyping(genv, constr, ty2, ty1, tag);
        }
        (TyKind::Ref(RefKind::Shr, ty1), TyKind::Ref(RefKind::Shr, ty2)) => {
            subtyping(genv, constr, ty1, ty2, tag);
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
                subtyping(genv, constr, ty1, ty2, tag);
            }
        }
        (_, TyKind::Constr(p2, ty2)) => {
            constr.push_head(p2.clone(), tag);
            subtyping(genv, constr, ty1, ty2, tag);
        }
        (TyKind::Constr(p1, ty1), _) => {
            constr.push_guard(p1.clone());
            subtyping(genv, constr, ty1, ty2, tag);
        }
        _ => unreachable!("`{ty1:?}` <: `{ty2:?}`"),
    }
}

fn arg_subtyping(constr: &mut ConstrBuilder, arg1: &RefineArg, arg2: &RefineArg, tag: Tag) {
    if arg1 == arg2 {
        return;
    }
    match (arg1, arg2) {
        (RefineArg::Expr(e1), RefineArg::Expr(e2)) => {
            constr.push_head(Expr::binary_op(BinOp::Eq, e1, e2), tag);
        }
        (RefineArg::Abs(abs1), RefineArg::Abs(abs2)) => {
            debug_assert_eq!(abs1.params(), abs2.params());
            let args = constr
                .define_vars(abs1.params())
                .into_iter()
                .map(|var| RefineArg::Expr(var.into()))
                .collect_vec();
            let pred1 = abs1.replace_bound_vars(&args);
            let pred2 = abs2.replace_bound_vars(&args);
            constr.push_horn_clause(&pred1, &pred2, tag);
            constr.push_horn_clause(pred2, pred1, tag);
        }
        (RefineArg::Expr(expr), RefineArg::Abs(abs))
        | (RefineArg::Abs(abs), RefineArg::Expr(expr)) => {
            if let ExprKind::FreeVar(name) = expr.kind() {
                let args = constr
                    .define_vars(abs.params())
                    .into_iter()
                    .map(Expr::from)
                    .collect_vec();
                let pred1 = Pred::App(Var::Free(*name), List::from(&args[..]));
                let args = args.into_iter().map(RefineArg::from).collect_vec();
                let pred2 = abs.replace_bound_vars(&args);
                constr.push_horn_clause(&pred1, &pred2, tag);
                constr.push_horn_clause(pred2, pred1, tag);
            } else {
                unreachable!("invalid refinement argument subtyping `{arg1:?}` - `{arg2:?}`")
            }
        }
    }
}

fn bty_subtyping(
    genv: &GlobalEnv,
    constr: &mut ConstrBuilder,
    bty1: &BaseTy,
    bty2: &BaseTy,
    tag: Tag,
) {
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
            let variances = genv.variances_of(def1.def_id());
            for (variance, ty1, ty2) in izip!(variances, substs1.iter(), substs2.iter()) {
                generic_arg_subtyping(genv, constr, *variance, ty1, ty2, tag);
            }
        }
        (BaseTy::Float(float_ty1), BaseTy::Float(float_ty2)) => {
            debug_assert_eq!(float_ty1, float_ty2);
        }
        (BaseTy::Bool, BaseTy::Bool) | (BaseTy::Str, BaseTy::Str) => {}
        (BaseTy::Array(ty1, len1), BaseTy::Array(ty2, len2)) => {
            debug_assert_eq!(len1, len2);
            subtyping(genv, constr, ty1, ty2, tag);
        }
        (BaseTy::Slice(ty1), BaseTy::Slice(ty2)) => {
            subtyping(genv, constr, ty1, ty2, tag);
        }
        (BaseTy::Char, BaseTy::Char) => {}
        _ => {
            unreachable!("unexpected base types: `{:?}` and `{:?}` at {:?}", bty1, bty2, tag.span())
        }
    }
}

fn generic_arg_subtyping(
    genv: &GlobalEnv,
    constr: &mut ConstrBuilder,
    variance: Variance,
    arg1: &GenericArg,
    arg2: &GenericArg,
    tag: Tag,
) {
    match (arg1, arg2) {
        (GenericArg::Ty(ty1), GenericArg::Ty(ty2)) => {
            match variance {
                rustc_middle::ty::Variance::Covariant => subtyping(genv, constr, ty1, ty2, tag),
                rustc_middle::ty::Variance::Invariant => {
                    subtyping(genv, constr, ty1, ty2, tag);
                    subtyping(genv, constr, ty2, ty1, tag);
                }
                rustc_middle::ty::Variance::Contravariant => subtyping(genv, constr, ty2, ty1, tag),
                rustc_middle::ty::Variance::Bivariant => {}
            }
        }
        (GenericArg::Lifetime, GenericArg::Lifetime) => {}
        _ => unreachable!("incompatible generic args:  `{arg1:?}` `{arg2:?}"),
    };
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
