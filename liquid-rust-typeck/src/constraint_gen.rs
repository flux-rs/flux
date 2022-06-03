use std::iter;

use itertools::{izip, Itertools};

use rustc_span::Span;

use liquid_rust_middle::{
    global_env::{GlobalEnv, Variance},
    rustc::mir::BasicBlock,
    ty::{BaseTy, BinOp, Constr, Expr, Index, Pred, RefKind, Ty, TyKind},
};

use crate::{
    refine_tree::{ConstrBuilder, RefineCtxt},
    type_env::TypeEnv,
};

pub struct ConstraintGen<'a, 'tcx> {
    pub genv: &'a GlobalEnv<'tcx>,
    builder: ConstrBuilder<'a>,
    tag: Tag,
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

impl<'a, 'tcx> ConstraintGen<'a, 'tcx> {
    pub fn new(genv: &'a GlobalEnv<'tcx>, rcx: &'a mut RefineCtxt, tag: Tag) -> Self {
        ConstraintGen { genv, builder: rcx.check_constr(), tag }
    }

    pub fn check_constr(&mut self, env: &mut TypeEnv, constr: &Constr) {
        match constr {
            Constr::Type(path, ty) => {
                let actual_ty = env.lookup_path(&path.expect_path());
                self.subtyping(&actual_ty, ty);
            }
            Constr::Pred(e) => {
                self.check_pred(e.clone());
            }
        }
    }

    pub fn check_pred(&mut self, pred: impl Into<Pred>) {
        self.builder.push_head(pred, self.tag);
    }

    pub fn subtyping(&mut self, ty1: &Ty, ty2: &Ty) {
        subtyping(self.genv, &mut self.builder, ty1, ty2, self.tag)
    }
}

pub fn subtyping(genv: &GlobalEnv, builder: &mut ConstrBuilder, ty1: &Ty, ty2: &Ty, tag: Tag) {
    let builder = &mut builder.breadcrumb();
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Indexed(bty1, e1), TyKind::Indexed(bty2, e2)) if e1 == e2 => {
            bty_subtyping(genv, builder, bty1, bty2, tag);
            return;
        }
        (TyKind::Exists(bty1, p1), TyKind::Exists(bty2, p2)) if p1 == p2 => {
            bty_subtyping(genv, builder, bty1, bty2, tag);
            return;
        }
        (TyKind::Exists(bty, pred), _) => {
            let indices = builder
                .push_binders(pred)
                .into_iter()
                .map(|name| Index::from(Expr::fvar(name)))
                .collect_vec();
            let ty1 = Ty::indexed(bty.clone(), indices);
            subtyping(genv, builder, &ty1, ty2, tag);
            return;
        }
        _ => {}
    }

    match (ty1.kind(), ty2.kind()) {
        (TyKind::Indexed(bty1, exprs1), TyKind::Indexed(bty2, exprs2)) => {
            bty_subtyping(genv, builder, bty1, bty2, tag);
            for (e1, e2) in iter::zip(exprs1, exprs2) {
                builder.push_head(Expr::binary_op(BinOp::Eq, e1.clone(), e2.clone()), tag);
            }
        }
        (TyKind::Indexed(bty1, indices), TyKind::Exists(bty2, pred)) => {
            bty_subtyping(genv, builder, bty1, bty2, tag);
            let exprs = indices.iter().map(|idx| idx.expr.clone()).collect_vec();
            builder.push_head(pred.replace_bound_vars(&exprs), tag);
        }
        (TyKind::Ptr(loc1), TyKind::Ptr(loc2)) => {
            assert_eq!(loc1, loc2);
        }
        (TyKind::Ref(RefKind::Mut, ty1), TyKind::Ref(RefKind::Mut, ty2)) => {
            variance_subtyping(genv, builder, Variance::Invariant, ty1, ty2, tag);
        }
        (TyKind::Ref(RefKind::Shr, ty1), TyKind::Ref(RefKind::Shr, ty2)) => {
            subtyping(genv, builder, ty1, ty2, tag);
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
                subtyping(genv, builder, ty1, ty2, tag);
            }
        }
        _ => todo!("`{ty1:?}` <: `{ty2:?}`"),
    }
}

fn bty_subtyping(
    genv: &GlobalEnv,
    builder: &mut ConstrBuilder,
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
                variance_subtyping(genv, builder, *variance, ty1, ty2, tag);
            }
        }
        _ => unreachable!("unexpected base types: `{:?}` `{:?}`", bty1, bty2),
    }
}

fn variance_subtyping(
    genv: &GlobalEnv,
    builder: &mut ConstrBuilder,
    variance: Variance,
    ty1: &Ty,
    ty2: &Ty,
    tag: Tag,
) {
    match variance {
        rustc_middle::ty::Variance::Covariant => {
            subtyping(genv, builder, ty1, ty2, tag);
        }
        rustc_middle::ty::Variance::Invariant => {
            subtyping(genv, builder, ty1, ty2, tag);
            subtyping(genv, builder, ty2, ty1, tag);
        }
        rustc_middle::ty::Variance::Contravariant => {
            subtyping(genv, builder, ty2, ty1, tag);
        }
        rustc_middle::ty::Variance::Bivariant => {}
    }
}

mod pretty {
    use std::fmt;

    use super::*;
    use liquid_rust_middle::pretty::*;

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
