use std::collections::HashSet;

use flux_middle::rty;
use itertools::Itertools;
use liquid_fixpoint::{SuggestionSolver, SuggestionsZ3Backend, check_validity, qe_and_simplify};
use rustc_data_structures::fx::FxIndexMap;

use crate::{
    fixpoint_encoding::{
        ConstKey, FixpointCtxt, FixpointSolution, PossibleSolutions, SuggestionCtxt, TagIdx,
        fixpoint,
    },
    wkvars::WKVarInstantiator,
};

pub type TagToFlatConstraint = FxIndexMap<TagIdx, fixpoint::FlatConstraint>;

fn suggestions_z3_backend() -> SuggestionsZ3Backend {
    match flux_config::suggestions_z3() {
        flux_config::SuggestionsZ3::Bindings => SuggestionsZ3Backend::Bindings,
        flux_config::SuggestionsZ3::Process => SuggestionsZ3Backend::Process,
        flux_config::SuggestionsZ3::Compare => SuggestionsZ3Backend::Compare,
    }
}

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
) -> Result<PossibleSolutions, liquid_fixpoint::SuggestionSolverError>
where
    Tag: std::hash::Hash + Eq + Copy,
{
    let Some(flat_constraint) = suggestion_ctx.flat_constraints.get(&tag_idx) else {
        return Ok(Default::default());
    };
    let head_expr = match &flat_constraint.head {
        fixpoint::Pred::Expr(e) => Some(e.clone()),
        _ => None,
    };
    let mut possible_solutions: PossibleSolutions = Default::default();
    let mut solver = SuggestionSolver::new(suggestions_z3_backend())?;
    let wkvars_and_constraints = flat_constraint.wkvars_and_constrs();
    for (wkvar, flat_constraint, other_constrs) in wkvars_and_constraints {
        let mut valid = true;
        for other_constr in other_constrs {
            let binder_consts = other_constr
                .binders
                .iter()
                .map(|(var, sort)| {
                    fixpoint::ConstDecl { name: *var, sort: sort.clone(), comment: None }
                })
                .collect_vec();
            if !check_validity(
                &mut solver,
                &other_constr,
                &binder_consts,
                &suggestion_ctx.const_decls,
                suggestion_ctx.data_decls.clone(),
            )? {
                valid = false;
                break;
            }
        }
        if !valid {
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
        let result = qe_and_simplify(
            &mut solver,
            &new_flat_constraint,
            &binder_consts,
            &suggestion_ctx.const_decls,
            suggestion_ctx.data_decls.clone(),
        );
        let fallback = head_expr
            .as_ref()
            .and_then(|head| fxctx.fixpoint_to_expr(head).ok())
            .and_then(|head| {
                WKVarInstantiator::try_instantiate_wkvar_args(self_args, &rty_args, &head)
            });
        let solution = match result {
            Ok(fe) => {
                match fxctx.fixpoint_to_expr(&fe) {
                    Ok(expr) if expr.is_trivially_false() || expr.is_trivially_true() => None,
                    Ok(_) if fe.total_num_disjuncts() > 3 => fallback,
                    Ok(expr) => {
                        WKVarInstantiator::try_instantiate_wkvar_args(self_args, &rty_args, &expr)
                            .or(fallback)
                    }
                    Err(_) => None,
                }
            }
            Err(_) => fallback,
        };
        if let Some(solution) = solution {
            possible_solutions
                .entry(wkvid.clone())
                .or_default()
                .push(solution);
        }
    }
    Ok(possible_solutions)
}
