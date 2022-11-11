use std::iter;

use flux_middle::rty::{
    subst::FVarSubst, BaseTy, Binders, Constraint, Expr, ExprKind, GenericArg, Name, Path, PolySig,
    PolyVariant, Pred, RefineArg, Sort, Ty, TyKind, INNERMOST,
};
use rustc_hash::FxHashMap;

use crate::type_env::PathMap;

type Exprs = FxHashMap<usize, Expr>;

#[derive(Debug, Eq, PartialEq)]
pub struct InferenceError(String);

pub fn infer_from_constructor(
    fields: &[Ty],
    variant: &PolyVariant,
    fresh_kvar: &mut impl FnMut(&[Sort]) -> Binders<Pred>,
) -> Result<Vec<RefineArg>, InferenceError> {
    debug_assert_eq!(fields.len(), variant.as_ref().skip_binders().fields().len());
    let mut exprs = Exprs::default();

    for (actual, formal) in iter::zip(fields, variant.as_ref().skip_binders().fields()) {
        infer_from_tys(&mut exprs, &FxHashMap::default(), actual, &FxHashMap::default(), formal);
    }

    collect(variant, exprs, fresh_kvar)
}

pub fn infer_from_fn_call<M: PathMap>(
    env: &M,
    actuals: &[Ty],
    fn_sig: &PolySig,
    fresh_kvar: &mut impl FnMut(&[Sort]) -> Binders<Pred>,
) -> Result<Vec<RefineArg>, InferenceError> {
    debug_assert_eq!(actuals.len(), fn_sig.as_ref().skip_binders().args().len());

    let mut exprs = Exprs::default();
    let requires: FxHashMap<Path, Ty> = fn_sig
        .as_ref()
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

    for (actual, formal) in iter::zip(actuals, fn_sig.as_ref().skip_binders().args()) {
        infer_from_tys(&mut exprs, env, actual, &requires, formal);
    }

    collect(fn_sig, exprs, fresh_kvar)
}

fn collect<T>(
    t: &Binders<T>,
    mut exprs: Exprs,
    fresh_kvar: &mut impl FnMut(&[Sort]) -> Binders<Pred>,
) -> Result<Vec<RefineArg>, InferenceError> {
    t.params()
        .iter()
        .enumerate()
        .map(|(idx, sort)| {
            if let Sort::Func(fsort) = sort && fsort.output().is_bool() {
                Ok(RefineArg::Abs(fresh_kvar(fsort.inputs())))
            } else {
                let e = exprs
                    .remove(&idx)
                    .ok_or_else(|| InferenceError(format!("^0.{idx}")))?;
                Ok(RefineArg::Expr(e))
            }
        })
        .collect()
}

pub fn check_inference(
    subst: &FVarSubst,
    params: impl Iterator<Item = Name>,
) -> Result<(), InferenceError> {
    for name in params {
        if !subst.contains(name) {
            return Err(InferenceError(format!("{name:?}")));
        }
    }
    Ok(())
}

fn infer_from_tys(exprs: &mut Exprs, env1: &impl PathMap, ty1: &Ty, env2: &impl PathMap, ty2: &Ty) {
    match (ty1.unconstr().kind(), ty2.unconstr().kind()) {
        (TyKind::Indexed(_, idxs1), TyKind::Indexed(_, idxs2)) => {
            for (i, (idx1, idx2)) in iter::zip(idxs1.args(), idxs2.args()).enumerate() {
                if idxs2.is_binder(i) {
                    infer_from_refine_args(exprs, idx1, idx2);
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

fn infer_from_btys(
    exprs: &mut Exprs,
    env1: &impl PathMap,
    ty1: &Ty,
    env2: &impl PathMap,
    ty2: &Ty,
) {
    if let Some(bt1) = ty1.bty() &&
       let Some(bt2) = ty2.bty() &&
       let BaseTy::Adt(_, args1) = bt1 &&
       let BaseTy::Adt(_, args2) = bt2 &&
       bt1.is_box() {
            for (arg1, arg2) in iter::zip(args1, args2) {
                infer_from_generic_args(exprs, env1, arg1, env2, arg2);
            }
       }
}

fn infer_from_generic_args(
    exprs: &mut Exprs,
    env1: &impl PathMap,
    arg1: &GenericArg,
    env2: &impl PathMap,
    arg2: &GenericArg,
) {
    if let (GenericArg::Ty(ty1), GenericArg::Ty(ty2)) = (arg1, arg2) {
        infer_from_tys(exprs, env1, ty1, env2, ty2)
    }
}

fn infer_from_refine_args(exprs: &mut Exprs, arg1: &RefineArg, arg2: &RefineArg) {
    if let (RefineArg::Expr(e1), RefineArg::Expr(e2)) = (arg1, arg2) {
        infer_from_exprs(exprs, e1, e2)
    }
}

fn infer_from_exprs(exprs: &mut Exprs, e1: &Expr, e2: &Expr) {
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
