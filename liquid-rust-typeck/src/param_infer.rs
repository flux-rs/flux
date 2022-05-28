use std::iter;

use rustc_hash::{FxHashMap, FxHashSet};

use liquid_rust_middle::{
    global_env::GlobalEnv,
    ty::{subst::Subst, Constr, Expr, ExprKind, Name, Path, PolySig, Ty, TyKind},
};

use crate::{refine_tree::RefineCtxt, type_env::TypeEnv};

#[derive(Debug, Eq, PartialEq)]
pub struct InferenceError(Name);

pub fn infer_from_fn_call(
    subst: &mut Subst,
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    env: &TypeEnv,
    actuals: &[Ty],
    fn_sig: &PolySig,
) -> Result<(), InferenceError> {
    assert!(actuals.len() == fn_sig.value().args().len());
    let params = fn_sig.params().iter().map(|param| param.name).collect();

    let requires = fn_sig
        .value()
        .requires()
        .iter()
        .filter_map(|constr| {
            if let Constr::Type(path, ty) = constr {
                Some((path.expect_path(), ty.clone()))
            } else {
                None
            }
        })
        .collect();

    for (actual, formal) in actuals.iter().zip(fn_sig.value().args().iter()) {
        infer_from_tys(subst, genv, rcx, &params, env, actual, &requires, formal);
    }

    check_inference(subst, params.into_iter())
}

pub fn check_inference(
    subst: &Subst,
    params: impl Iterator<Item = Name>,
) -> Result<(), InferenceError> {
    for name in params {
        if !subst.contains(name) {
            return Err(InferenceError(name));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn infer_from_tys(
    subst: &mut Subst,
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    params: &FxHashSet<Name>,
    env: &TypeEnv,
    ty1: &Ty,
    requires: &FxHashMap<Path, Ty>,
    ty2: &Ty,
) {
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Indexed(_, indices1), TyKind::Indexed(_, indices2)) => {
            for (idx1, idx2) in iter::zip(indices1, indices2) {
                if idx2.is_binder {
                    infer_from_exprs(subst, params, &idx1.expr, &idx2.expr);
                }
            }
        }
        (TyKind::Exists(bty1, p), TyKind::Indexed(_, indices2)) => {
            // HACK(nilehmann) we should probably remove this once we have proper unpacking of &mut refs
            let sorts = genv.sorts(bty1);
            let names1 = rcx.define_params(&sorts, p);
            for (name1, idx2) in iter::zip(names1, indices2) {
                if idx2.is_binder {
                    infer_from_exprs(subst, params, &Expr::fvar(name1), &idx2.expr);
                }
            }
        }
        (TyKind::Ptr(path1), TyKind::Ref(_, ty2)) => {
            infer_from_tys(
                subst,
                genv,
                rcx,
                params,
                env,
                &env.lookup_path(&path1.expect_path()),
                requires,
                ty2,
            );
        }
        (TyKind::Ptr(path1), TyKind::Ptr(path2)) => {
            infer_from_exprs(subst, params, path1, path2);
            infer_from_tys(
                subst,
                genv,
                rcx,
                params,
                env,
                &env.lookup_path(&path1.expect_path()),
                requires,
                &requires[&path2.expect_path()],
            );
        }
        (TyKind::Ref(mode1, ty1), TyKind::Ref(mode2, ty2)) => {
            debug_assert_eq!(mode1, mode2);
            infer_from_tys(subst, genv, rcx, params, env, ty1, requires, ty2);
        }
        _ => {}
    }
}

pub fn infer_from_exprs(subst: &mut Subst, params: &FxHashSet<Name>, e1: &Expr, e2: &Expr) {
    match (e1.kind(), e2.kind()) {
        (_, ExprKind::FreeVar(name)) if params.contains(name) => {
            if let Some(old_e) = subst.insert(*name, e1.clone()) {
                if &old_e != e2 {
                    todo!(
                        "ambiguous instantiation for parameter: {:?} -> [{:?}, {:?}]",
                        *name,
                        old_e,
                        e1
                    )
                }
            }
        }
        (ExprKind::Tuple(exprs1), ExprKind::Tuple(exprs2)) => {
            debug_assert_eq!(exprs1.len(), exprs2.len());
            for (e1, e2) in exprs1.iter().zip(exprs2) {
                infer_from_exprs(subst, params, e1, e2);
            }
        }
        (ExprKind::PathProj(e1, field1), ExprKind::PathProj(e2, field2)) if field1 == field2 => {
            infer_from_exprs(subst, params, e1, e2);
        }
        _ => {}
    }
}
