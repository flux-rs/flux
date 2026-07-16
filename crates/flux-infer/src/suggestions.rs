use std::collections::HashSet;

use flux_middle::rty;
use itertools::Itertools;
use liquid_fixpoint::{check_validity, qe_and_simplify};
use rustc_data_structures::fx::FxIndexMap;

use crate::{
    fixpoint_encoding::{
        ConstKey, FixpointCtxt, FixpointSolution, PossibleSolutions, SuggestionCtxt, TagIdx,
        fixpoint,
    },
    wkvars::WKVarInstantiator,
};

pub type TagToFlatConstraint = FxIndexMap<TagIdx, fixpoint::FlatConstraint>;

pub(crate) fn make_flat_constraint_map(constraint: &fixpoint::Constraint) -> TagToFlatConstraint {
    constraint
        .flatten(|var| matches!(var, fixpoint::Var::Underscore))
        .into_iter()
        .flat_map(|flat_constraint| {
            // We can't send a kvar to the SMT. If there's a kvar on the LHS we
            // can underapproximate it with TRUE, but if it's in head position
            // we don't know what to do.
            if let Some(tag) = flat_constraint.tag
                && !matches!(flat_constraint.head, fixpoint::Pred::KVar(..))
            {
                Some((tag.clone(), flat_constraint))
            } else {
                None
            }
        })
        .collect()
}

pub(crate) fn subst_fixpoint_solutions(
    flat_constraint: &mut fixpoint::FlatConstraint,
    fixpoint_solution: &FxIndexMap<fixpoint::KVid, FixpointSolution>,
) {
    flat_constraint.assumptions = flat_constraint
        .assumptions
        .iter()
        .flat_map(|pred| {
            // Remove all trivially true assumptions
            if pred.is_trivially_true() {
                vec![].into_iter()
            // Substitute the kvar solutions in
            } else if let fixpoint::Pred::KVar(kvid, args) = pred
                && let Some((var_sorts, solution)) = &fixpoint_solution.get(kvid)
            {
                assert!(var_sorts.len() == args.len());
                let subst = args
                    .into_iter()
                    .zip(var_sorts.iter())
                    .map(|(arg, (subst_var, _))| (subst_var.clone(), arg.clone()))
                    .collect();
                let subst_solution = solution.substitute(&subst);
                subst_solution
                    .as_conjunction()
                    .into_iter()
                    .map(|expr| fixpoint::Pred::Expr(expr))
                    .collect_vec()
                    .into_iter()
            } else {
                vec![pred.clone()].into_iter()
            }
        })
        .collect();
}

pub(crate) fn find_possible_solutions<'genv, 'tcx, Tag>(
    fxctx: &mut FixpointCtxt<'genv, 'tcx, Tag>,
    tag_idx: TagIdx,
    suggestion_ctx: &SuggestionCtxt,
) -> PossibleSolutions
where
    Tag: std::hash::Hash + Eq + Copy,
{
    let Some(flat_constraint) = suggestion_ctx.flat_constraints.get(&tag_idx) else {
        return Default::default();
    };
    let head_expr = match &flat_constraint.head {
        fixpoint::Pred::Expr(e) => Some(e.clone()),
        _ => None,
    };
    let mut possible_solutions: PossibleSolutions = Default::default();
    let wkvars_and_constraints = flat_constraint.wkvars_and_constrs();
    for (wkvar, flat_constraint, other_constrs) in wkvars_and_constraints {
        if !other_constrs.iter().all(|other_constr| {
            let binder_consts = other_constr
                .binders
                .iter()
                .map(|(var, sort)| {
                    fixpoint::ConstDecl { name: *var, sort: sort.clone(), comment: None }
                })
                .collect_vec();
            check_validity(
                &other_constr,
                &binder_consts,
                &suggestion_ctx.const_decls,
                suggestion_ctx.data_decls.clone(),
            )
        }) {
            continue;
        }
        let ConstKey::WKVar(wkvid, self_args) = fxctx
            .ecx
            .const_env
            .wkvar_map_rev
            .get(&wkvar.wkvid)
            .cloned()
            .unwrap()
        else {
            panic!()
        };
        let fvars: HashSet<fixpoint::Var> = wkvar
            .args
            .iter()
            .flat_map(|arg| {
                arg.free_vars().into_iter().filter(|fvar| {
                    match fvar {
                        fixpoint::Var::Local(_) | fixpoint::Var::Param(_) => true,
                        _ => false,
                    }
                })
            })
            .collect();
        let rty_args: Vec<rty::Expr> = wkvar
            .args
            .iter()
            .map(|arg| fxctx.fixpoint_to_expr(arg))
            .try_collect()
            .unwrap();
        let (binder_consts, mut new_flat_constraint) = flat_constraint.remove_binders(&fvars);
        // Remove any wkvars and drop assumptions that are just wkvars or true
        new_flat_constraint.assumptions = new_flat_constraint
            .assumptions
            .into_iter()
            .filter_map(|assumption| {
                let assumption = assumption.strip_wkvars();
                if !assumption.is_trivially_true() { Some(assumption) } else { None }
            })
            .collect();
        match qe_and_simplify(
            &new_flat_constraint,
            &binder_consts,
            &suggestion_ctx.const_decls,
            suggestion_ctx.data_decls.clone(),
        ) {
            Ok(fe) => {
                match fxctx.fixpoint_to_expr(&fe) {
                    Ok(e) => {
                        if !e.is_trivially_false() && !e.is_trivially_true() {
                            if let Some(binder_e) = WKVarInstantiator::try_instantiate_wkvar_args(
                                self_args, &rty_args, &e,
                            ) {
                                if fe.total_num_disjuncts() > 3 {
                                    // NOTE: previously used blame_ctx.expr
                                    if let Some(binder_e) =
                                        WKVarInstantiator::try_instantiate_wkvar_args(
                                            self_args,
                                            &rty_args,
                                            &fxctx
                                                .fixpoint_to_expr(head_expr.as_ref().unwrap())
                                                .unwrap(),
                                        )
                                    {
                                        possible_solutions
                                            .entry(wkvid.clone())
                                            .or_default()
                                            .push(binder_e);
                                    }
                                } else {
                                    possible_solutions
                                        .entry(wkvid.clone())
                                        .or_default()
                                        .push(binder_e);
                                }
                            } else {
                                // NOTE: previously used blame_ctx.expr
                                if let Some(binder_e) =
                                    WKVarInstantiator::try_instantiate_wkvar_args(
                                        self_args,
                                        &rty_args,
                                        &fxctx
                                            .fixpoint_to_expr(head_expr.as_ref().unwrap())
                                            .unwrap(),
                                    )
                                {
                                    possible_solutions
                                        .entry(wkvid.clone())
                                        .or_default()
                                        .push(binder_e);
                                }
                            }
                        } else {
                            // skip trivial solution
                        }
                    }
                    Err(_err) => {}
                }
            }
            Err(_err) => {
                // NOTE: previously used blame_ctx.expr
                if let Some(binder_e) = WKVarInstantiator::try_instantiate_wkvar_args(
                    self_args,
                    &rty_args,
                    &fxctx.fixpoint_to_expr(head_expr.as_ref().unwrap()).unwrap(),
                ) {
                    possible_solutions
                        .entry(wkvid.clone())
                        .or_default()
                        .push(binder_e);
                }
            }
        }
    }
    possible_solutions
}
