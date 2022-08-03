use std::iter;

use itertools::{izip, Itertools};

use rustc_span::Span;

use flux_middle::{
    global_env::{GlobalEnv, Variance},
    rustc::mir::BasicBlock,
    ty::{
        fold::TypeFoldable, BaseTy, BinOp, Constraint, Constraints, Expr, Index, PolySig, Pred,
        RefKind, Sort, Ty, TyKind,
    },
};

use crate::{
    param_infer::{self, InferenceError},
    refine_tree::{ConstrBuilder, RefineCtxt},
    type_env::PathMap,
};

#[allow(clippy::type_complexity)]
pub struct ConstrGen<'a, 'tcx> {
    pub genv: &'a GlobalEnv<'a, 'tcx>,
    fresh_kvar: Box<dyn FnMut(&[Sort]) -> Pred + 'a>,
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
        F: FnMut(&[Sort]) -> Pred + 'a,
    {
        ConstrGen { genv, fresh_kvar: Box::new(fresh_kvar), tag }
    }

    pub fn check_constraint<Env: PathMap>(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut Env,
        constraint: &Constraint,
    ) {
        let mut constr = rcx.check_constr();
        check_constraint(self.genv, env, constraint, self.tag, &mut constr);
    }

    pub fn check_pred(&mut self, rcx: &mut RefineCtxt, pred: impl Into<Pred>) {
        let mut constr = rcx.check_constr();
        constr.push_head(pred, self.tag);
    }

    pub fn subtyping(&mut self, rcx: &mut RefineCtxt, ty1: &Ty, ty2: &Ty) {
        let mut constr = rcx.check_constr();
        subtyping(self.genv, &mut constr, ty1, ty2, self.tag)
    }

    pub fn check_fn_call<Env: PathMap>(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut Env,
        fn_sig: &PolySig,
        substs: &[Ty],
        actuals: &[Ty],
    ) -> Result<CallOutput, InferenceError> {
        // HACK(nilehmann) This let us infer parameters under mutable references for the simple case
        // where the formal argument is of the form `&mut B[@n]`, e.g., the type of the first argument
        // to `RVec::get_mut` is `&mut RVec<T>[@n]`. We should remove this after we implement opening of
        // mutable references.
        let actuals = iter::zip(actuals, fn_sig.skip_binders().args())
            .map(|(actual, formal)| {
                if let (TyKind::Ref(RefKind::Mut, _), TyKind::Ref(RefKind::Mut, ty)) = (actual.kind(), formal.kind())
                && let TyKind::Indexed(..) = ty.kind() {
                    rcx.unpack(actual, true)
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
        let exprs = param_infer::infer_from_fn_call(env, &actuals, fn_sig)?;
        let fn_sig = fn_sig
            .replace_generic_types(&substs)
            .replace_bound_vars(&exprs);

        // Check arguments
        let constr = &mut rcx.check_constr();
        for (actual, formal) in iter::zip(actuals, fn_sig.args()) {
            if let (TyKind::Ptr(path), TyKind::Ref(RefKind::Mut, bound)) =
                (actual.kind(), formal.kind())
            {
                subtyping(self.genv, constr, &env.get(path), bound, self.tag);
                env.update(path, bound.clone());
            } else {
                subtyping(self.genv, constr, &actual, formal, self.tag);
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
        (TyKind::Indexed(bty1, idxs1), TyKind::Indexed(bty2, idx2)) => {
            bty_subtyping(genv, constr, bty1, bty2, tag);
            for (idx1, idx2) in iter::zip(idxs1, idx2) {
                if idx1.expr != idx2.expr {
                    constr.push_head(Expr::binary_op(BinOp::Eq, idx1.clone(), idx2.clone()), tag);
                }
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

        (_, TyKind::Constr(p2, ty2)) => {
            constr.push_head(p2.clone(), tag);
            subtyping(genv, constr, ty1, ty2, tag)
        }
        (TyKind::Constr(p1, ty1), _) => {
            constr.push_guard(p1.clone());
            subtyping(genv, constr, ty1, ty2, tag)
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
        _ => {
            unreachable!("unexpected base types: `{:?}` and `{:?}` at {:?}", bty1, bty2, tag.span())
        }
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
    use flux_middle::pretty::*;
    use std::fmt;

    impl Pretty for Tag {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(_cx, f);
            match self {
                Tag::Call(span) => w!("Call({:?})", span),
                Tag::Assign(span) => w!("Assign({:?})", span),
                Tag::Ret => w!("Ret"),
                Tag::RetAt(span) => w!("RetAt({:?}", span),
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
            }
        }
    }
}
