use std::iter;

use flux_middle::rty::{
    subst::FVarSubst, BaseTy, Binders, Constraint, Expr, ExprKind, Name, Path, PolySig,
    PolyVariant, Ty, TyKind, INNERMOST,
};
use rustc_hash::FxHashMap;

use crate::type_env::PathMap;

type Exprs = FxHashMap<usize, Expr>;

#[derive(Debug, Eq, PartialEq)]
pub struct InferenceError;

pub fn infer_from_constructor(
    fields: &[Ty],
    variant: &PolyVariant,
) -> Result<Vec<Expr>, InferenceError> {
    debug_assert_eq!(fields.len(), variant.skip_binders().fields().len());
    let mut exprs = Exprs::default();

    for (actual, formal) in iter::zip(fields, variant.skip_binders().fields()) {
        infer_from_tys(&mut exprs, &FxHashMap::default(), actual, &FxHashMap::default(), formal);
    }

    collect(variant, exprs)
}

pub fn infer_from_fn_call<M: PathMap>(
    env: &M,
    actuals: &[Ty],
    fn_sig: &PolySig,
) -> Result<Vec<Expr>, InferenceError> {
    debug_assert_eq!(actuals.len(), fn_sig.skip_binders().args().len());

    let mut exprs = Exprs::default();
    let requires: FxHashMap<Path, Ty> = fn_sig
        .skip_binders()
        .requires()
        .iter()
        .filter_map(|constr| {
            if let Constraint::Type(path, ty) = constr {
                Some((path.clone(), ty.clone()))
            } else {
                None
            }
        })
        .collect();

    for (actual, formal) in iter::zip(actuals, fn_sig.skip_binders().args()) {
        infer_from_tys(&mut exprs, env, actual, &requires, formal);
    }

    collect(fn_sig, exprs)
}

fn collect<T>(t: &Binders<T>, mut exprs: Exprs) -> Result<Vec<Expr>, InferenceError> {
    t.params()
        .iter()
        .enumerate()
        .map(|(idx, _)| exprs.remove(&idx).ok_or(InferenceError))
        .collect()
}

pub fn check_inference(
    subst: &FVarSubst,
    params: impl Iterator<Item = Name>,
) -> Result<(), InferenceError> {
    for name in params {
        if !subst.contains(name) {
            return Err(InferenceError);
        }
    }
    Ok(())
}
fn infer_from_tys<M1: PathMap, M2: PathMap>(
    exprs: &mut Exprs,
    env1: &M1,
    ty1: &Ty,
    env2: &M2,
    ty2: &Ty,
) {
    match (ty1.unconstr().kind(), ty2.unconstr().kind()) {
        (TyKind::Indexed(_, indices1), TyKind::Indexed(_, indices2)) => {
            for (idx1, idx2) in iter::zip(indices1, indices2) {
                if idx2.is_binder {
                    infer_from_exprs(exprs, &idx1.expr, &idx2.expr);
                }
            }
        }
        (TyKind::Ptr(rk1, path1), TyKind::Ref(rk2, ty2)) => {
            debug_assert_eq!(rk1, rk2);
            infer_from_tys(exprs, env1, &env1.get(path1), env2, ty2);
        }
        (TyKind::Ptr(rk1, path1), TyKind::Ptr(rk2, path2)) => {
            debug_assert_eq!(rk1, rk2);
            infer_from_exprs(exprs, &path1.to_expr(), &path2.to_expr());
            infer_from_tys(exprs, env1, &env1.get(path1), env2, &env2.get(path2));
        }
        (TyKind::Ref(rk1, ty1), TyKind::Ref(rk2, ty2)) => {
            debug_assert_eq!(rk1, rk2);
            infer_from_tys(exprs, env1, ty1, env2, ty2);
        }
        _ => {}
    }
    infer_from_btys(exprs, env1, ty1, env2, ty2);
}

fn infer_from_btys<M1: PathMap, M2: PathMap>(
    exprs: &mut Exprs,
    env1: &M1,
    ty1: &Ty,
    env2: &M2,
    ty2: &Ty,
) {
    if let Some(bt1) = ty1.bty() &&
       let Some(bt2) = ty2.bty() &&
       let BaseTy::Adt(_, args1) = bt1 &&
       let BaseTy::Adt(_, args2) = bt2 &&
       bt1.is_box() {
            for (arg1, arg2) in iter::zip(args1, args2) {
                infer_from_tys(exprs, env1, arg1, env2, arg2);
            }
       }
}

pub fn infer_from_exprs(exprs: &mut Exprs, e1: &Expr, e2: &Expr) {
    match (e1.kind(), e2.kind()) {
        (_, ExprKind::BoundVar(bvar)) if bvar.debruijn == INNERMOST => {
            if let Some(old_e) = exprs.insert(bvar.index, e1.clone()) {
                if &old_e != e1 {
                    todo!(
                        "ambiguous instantiation for parameter: {:?} -> [{:?}, {:?}]",
                        bvar,
                        old_e,
                        e1
                    )
                }
            }
        }
        (ExprKind::Tuple(exprs1), ExprKind::Tuple(exprs2)) => {
            debug_assert_eq!(exprs1.len(), exprs2.len());
            for (e1, e2) in exprs1.iter().zip(exprs2) {
                infer_from_exprs(exprs, e1, e2);
            }
        }
        (ExprKind::PathProj(e1, field1), ExprKind::PathProj(e2, field2)) if field1 == field2 => {
            infer_from_exprs(exprs, e1, e2);
        }
        _ => {}
    }
}
