use std::iter;

use rustc_hash::FxHashMap;

use liquid_rust_middle::ty::{
    subst::FVarSubst, Constraint, Expr, ExprKind, Name, Path, PolySig, Ty, TyKind, INNERMOST,
};

use crate::type_env::PathMap;

type Exprs = FxHashMap<usize, Expr>;

#[derive(Debug, Eq, PartialEq)]
pub struct InferenceError;

pub fn infer_from_fn_call<M: PathMap>(
    env: &M,
    actuals: &[Ty],
    fn_sig: &PolySig,
) -> Result<Vec<Expr>, InferenceError> {
    assert!(actuals.len() == fn_sig.skip_binders().args().len());

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

    for (actual, formal) in actuals.iter().zip(fn_sig.skip_binders().args().iter()) {
        infer_from_tys(&mut exprs, env, actual, &requires, formal);
    }

    fn_sig
        .params()
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
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Indexed(_, indices1), TyKind::Indexed(_, indices2)) => {
            for (idx1, idx2) in iter::zip(indices1, indices2) {
                if idx2.is_binder {
                    infer_from_exprs(exprs, &idx1.expr, &idx2.expr);
                }
            }
        }
        (TyKind::Ptr(path1), TyKind::Ref(_, ty2)) => {
            infer_from_tys(exprs, env1, &env1.get(path1), env2, ty2);
        }
        (TyKind::Ptr(path1), TyKind::Ptr(path2)) => {
            infer_from_exprs(exprs, &path1.to_expr(), &path2.to_expr());
            infer_from_tys(exprs, env1, &env1.get(path1), env2, &env2.get(path2));
        }
        (TyKind::Ref(mode1, ty1), TyKind::Ref(mode2, ty2)) => {
            debug_assert_eq!(mode1, mode2);
            infer_from_tys(exprs, env1, ty1, env2, ty2);
        }
        _ => {}
    }
}

pub fn infer_from_exprs(exprs: &mut Exprs, e1: &Expr, e2: &Expr) {
    match (e1.kind(), e2.kind()) {
        (_, ExprKind::BoundVar(bvar)) if bvar.debruijn == INNERMOST => {
            if let Some(old_e) = exprs.insert(bvar.index, e1.clone()) {
                if &old_e != e2 {
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
