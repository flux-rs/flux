use std::iter;

use itertools::{izip, Itertools};

use rustc_span::Span;

use liquid_rust_middle::{
    global_env::{GlobalEnv, Variance},
    rustc::mir::BasicBlock,
    ty::{
        fold::TypeFoldable, BaseTy, BinOp, Constraint, Constraints, Expr, Index, PolySig, Pred,
        RefKind, Ty, TyKind,
    },
};

use crate::{
    param_infer::{self, InferenceError},
    refine_tree::{ConstrBuilder, RefineCtxt},
    type_env::PathMap,
};

pub struct ConstrGen<'a, 'rcx, 'tcx> {
    genv: &'a GlobalEnv<'tcx>,
    rcx: &'a mut RefineCtxt<'rcx>,
    fresh_kvar: Box<dyn FnMut(&BaseTy) -> Pred + 'a>,
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
    Assert(&'static str, Span),
    Div(Span),
    Rem(Span),
    Goto(Option<Span>, BasicBlock),
}

impl<'a, 'rcx, 'tcx> ConstrGen<'a, 'rcx, 'tcx> {
    pub fn new<F>(
        genv: &'a GlobalEnv<'tcx>,
        rcx: &'a mut RefineCtxt<'rcx>,
        fresh_kvar: F,
        tag: Tag,
    ) -> Self
    where
        F: FnMut(&BaseTy) -> Pred + 'a,
    {
        ConstrGen { genv, rcx, fresh_kvar: Box::new(fresh_kvar), tag }
    }

    pub fn check_constraint<Env: PathMap>(&mut self, env: &mut Env, constraint: &Constraint) {
        let mut constr = self.rcx.check_constr();
        check_constraint(self.genv, env, constraint, self.tag, &mut constr);
    }

    pub fn check_pred(&mut self, pred: impl Into<Pred>) {
        let mut constr = self.rcx.check_constr();
        constr.push_head(pred, self.tag);
    }

    pub fn subtyping(&mut self, ty1: &Ty, ty2: &Ty) {
        let mut constr = self.rcx.check_constr();
        subtyping(self.genv, &mut constr, ty1, ty2, self.tag)
    }

    pub fn check_fn_call<Env: PathMap>(
        &mut self,
        env: &mut Env,
        fn_sig: &PolySig,
        substs: &[Ty],
        actuals: &[Ty],
    ) -> Result<CallOutput, InferenceError> {
        // Generate fresh kvars for generic types
        let substs = substs
            .iter()
            .map(|arg| arg.replace_holes(&mut self.fresh_kvar))
            .collect_vec();

        // Infer refinement parameters
        let exprs = param_infer::infer_from_fn_call(self.rcx, env, actuals, fn_sig)?;
        let fn_sig = fn_sig
            .replace_generic_types(&substs)
            .replace_bound_vars(&exprs);

        // Check arguments
        let constr = &mut self.rcx.check_constr();
        for (actual, formal) in iter::zip(actuals, fn_sig.args()) {
            if let (TyKind::Ptr(path), TyKind::Ref(RefKind::Mut, bound)) =
                (actual.kind(), formal.kind())
            {
                subtyping(self.genv, constr, &env.get(path), bound, self.tag);
                env.update(&path, bound.clone());
            } else {
                subtyping(self.genv, constr, actual, formal, self.tag);
            }
        }

        // Check preconditions
        for constraint in fn_sig.requires() {
            check_constraint(self.genv, env, constraint, self.tag, constr);
        }

        Ok(CallOutput { ret: fn_sig.ret().clone(), ensures: fn_sig.ensures().clone() })
    }
}

fn check_constraint<Env: PathMap>(
    genv: &GlobalEnv,
    env: &Env,
    constraint: &Constraint,
    tag: Tag,
    constr: &mut ConstrBuilder,
) {
    match constraint {
        Constraint::Type(path, ty) => {
            let actual_ty = env.get(path);
            subtyping(genv, constr, &actual_ty, ty, tag);
        }
        Constraint::Pred(e) => {
            constr.push_head(e.clone(), tag);
        }
    }
}

fn subtyping(genv: &GlobalEnv, constr: &mut ConstrBuilder, ty1: &Ty, ty2: &Ty, tag: Tag) {
    let constr = &mut constr.breadcrumb();
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Indexed(bty1, e1), TyKind::Indexed(bty2, e2)) if e1 == e2 => {
            bty_subtyping(genv, constr, bty1, bty2, tag);
            return;
        }
        (TyKind::Exists(bty1, p1), TyKind::Exists(bty2, p2)) if p1 == p2 => {
            bty_subtyping(genv, constr, bty1, bty2, tag);
            return;
        }
        (TyKind::Exists(bty, pred), _) => {
            let indices = constr
                .push_binders(pred)
                .into_iter()
                .map(|name| Index::from(Expr::fvar(name)))
                .collect_vec();
            let ty1 = Ty::indexed(bty.clone(), indices);
            subtyping(genv, constr, &ty1, ty2, tag);
            return;
        }
        _ => {}
    }

    match (ty1.kind(), ty2.kind()) {
        (TyKind::Indexed(bty1, exprs1), TyKind::Indexed(bty2, exprs2)) => {
            bty_subtyping(genv, constr, bty1, bty2, tag);
            for (e1, e2) in iter::zip(exprs1, exprs2) {
                constr.push_head(Expr::binary_op(BinOp::Eq, e1.clone(), e2.clone()), tag);
            }
        }
        (TyKind::Indexed(bty1, indices), TyKind::Exists(bty2, pred)) => {
            bty_subtyping(genv, constr, bty1, bty2, tag);
            let exprs = indices.iter().map(|idx| idx.expr.clone()).collect_vec();
            constr.push_head(pred.replace_bound_vars(&exprs), tag);
        }
        (TyKind::Ptr(loc1), TyKind::Ptr(loc2)) => {
            assert_eq!(loc1, loc2);
        }
        (TyKind::Ref(RefKind::Mut, ty1), TyKind::Ref(RefKind::Mut, ty2)) => {
            variance_subtyping(genv, constr, Variance::Invariant, ty1, ty2, tag);
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
        (TyKind::Exists(..), _) => unreachable!("subtyping with unpacked existential"),
        (TyKind::Float(float_ty1), TyKind::Float(float_ty2)) => {
            debug_assert_eq!(float_ty1, float_ty2);
        }
        (TyKind::Tuple(tys1), TyKind::Tuple(tys2)) => {
            debug_assert_eq!(tys1.len(), tys2.len());
            for (ty1, ty2) in iter::zip(tys1, tys2) {
                subtyping(genv, constr, ty1, ty2, tag);
            }
        }
        _ => todo!("`{ty1:?}` <: `{ty2:?}`"),
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
        (BaseTy::Bool, BaseTy::Bool) => {}
        (BaseTy::Adt(def1, substs1), BaseTy::Adt(def2, substs2)) => {
            debug_assert_eq!(def1.def_id(), def2.def_id());
            debug_assert_eq!(substs1.len(), substs2.len());
            let variances = genv.variances_of(def1.def_id());
            for (variance, ty1, ty2) in izip!(variances, substs1.iter(), substs2.iter()) {
                variance_subtyping(genv, constr, *variance, ty1, ty2, tag);
            }
        }
        _ => unreachable!("unexpected base types: `{:?}` `{:?}`", bty1, bty2),
    }
}

fn variance_subtyping(
    genv: &GlobalEnv,
    constr: &mut ConstrBuilder,
    variance: Variance,
    ty1: &Ty,
    ty2: &Ty,
    tag: Tag,
) {
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

mod pretty {
    use super::*;
    use liquid_rust_middle::pretty::*;
    use std::fmt;

    impl Pretty for Tag {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(_cx, f);
            match self {
                Tag::Call(span) => w!("Call({:?})", span),
                Tag::Assign(span) => w!("Assign({:?})", span),
                Tag::Ret => w!("Ret"),
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
            }
        }
    }
}
