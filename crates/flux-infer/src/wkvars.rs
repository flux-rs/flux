

use std::{
    collections::{ HashMap, hash_map::Entry, },
    ops::ControlFlow,
};

use flux_common::cache::QueryCache;
use flux_middle::{
    FixpointQueryKind, def_id::{self, MaybeExternId}, global_env::GlobalEnv, pretty, queries::QueryResult, rty::{
        self,
        fold::{
            FallibleTypeFolder, TypeFoldable, TypeFolder, TypeSuperFoldable, TypeVisitable,
            TypeVisitor,
        },
    }
};
use itertools::{Itertools, iproduct};
use liquid_fixpoint::SmtSolver;
use rustc_data_structures::{
    fx::{FxIndexMap, FxIndexSet, FxHashSet},
    snapshot_map::SnapshotMap,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_type_ir::{DebruijnIndex, INNERMOST};

use crate::{
    fixpoint_encoding::{BlameCtxt, FixpointCheckError, FixpointCtxt, KVarGen},
    infer::Tag,
    refine_tree::RefineTree,
};

pub struct WKVarInstantiator<'a> {
    /// Map from the actuals passed to this Weak KVar to its params
    ///
    /// In theory this could be a Vec<rty::Expr>, but the instantiator
    /// is configured right now to only return a single solution.
    args_to_param: &'a HashMap<rty::Expr, rty::Expr>,
    /// In theory, this could (and probably should) map to multiple
    /// solutions, i.e. a Vec<rty::Expr>.
    memo: &'a mut HashMap<rty::Expr, rty::Expr>,
    current_index: DebruijnIndex,
}

impl FallibleTypeFolder for WKVarInstantiator<'_> {
    /// We fail instantiation if we can't replace all free variables;
    /// return the name of the first unreplaceable free variable found.
    type Error = rty::Var;

    fn try_enter_binder(
        &mut self,
        _vars: &rty::BoundVariableKinds,
    ) {
        self.current_index.shift_in(1);
    }

    fn try_exit_binder(&mut self) {
        self.current_index.shift_out(1);
    }

    fn try_fold_expr(&mut self, e: &rty::Expr) -> Result<rty::Expr, rty::Var> {
        if let Some(instantiated_e) = self.memo.get(e) {
            return Ok(instantiated_e.clone());
        }

        // NOTE: In theory there is a choice here: either we substitute the
        // current expression for the parameter or we ignore it and continue
        // going. We'll choose to be greedy and always substitute if possible,
        // which I think will guarantee a solution if it exists, but I am not
        // sure.
        if let Some(param) = self.args_to_param.get(e) {
            let param_expr = param.shift_in_escaping(self.current_index.as_u32());
            self.memo.insert(e.clone(), param_expr.clone());
            return Ok(param_expr);
        }

        if let rty::ExprKind::Var(var) = e.kind() {
            // This is an escaping free var
            Err(*var)
        } else {
            let instantiated_expr = e.try_super_fold_with(self)?;
            self.memo.insert(e.clone(), instantiated_expr.clone());
            Ok(instantiated_expr)
        }
    }
}

impl WKVarInstantiator<'_> {
    /// If it succeeds: creates an expression that can replace the weak kvar,
    /// which when used as a refinement will produce the original expr in this
    /// branch after all substitutions have happened.
    ///
    /// FIXME: This does not properly deal with expressions that have bound variables:
    /// if the expression has a bound variable, we might fail the instantiation
    /// when it should succeed.
    pub fn try_instantiate_wkvar_args(
        wkvar_args: &[rty::Expr],
        expr: &rty::Expr,
    ) -> Option<rty::Binder<rty::Expr>> {
        println!("trying to instantiate {:?} using args {:?}", expr, wkvar_args);
        let expr_without_metadata = expr.erase_metadata();
        let expr_eta_expanded_rel = expr_without_metadata.expand_bin_rels();
        let mut args_to_param = HashMap::new();
        std::iter::zip(
            wkvar_args.iter().map(|arg| arg.erase_metadata()),
            // We'll make an instantiator that is generic because this instatiation
            // may (and probably will) be used in multiple places
            (0..wkvar_args.len()).into_iter().map(|var_num| {
                rty::Expr::bvar(INNERMOST, var_num.into(), rty::BoundReftKind::Anon)
            }),
        )
        .for_each(|(arg, param)| {
            ProductEtaExpander::eta_expand_products(param, arg, &mut args_to_param);
        });
        let mut instantiator = WKVarInstantiator {
            args_to_param: &args_to_param,
            memo: &mut HashMap::new(),
            // This remains 0 because we use it to track how to shift our params,
            // so the scope is the same.
            current_index: INNERMOST,
        };
        instantiator
            .try_fold_expr(&expr_eta_expanded_rel)
            .ok()
            .map(|instantiated_e| {
                rty::Binder::bind_with_sorts(
                    instantiated_e,
                    &std::iter::repeat_n(rty::Sort::Err, wkvar_args.len()).collect_vec(),
                )
            })
    }
}

pub struct WKVarSubst {
    pub wkvar_instantiations: HashMap<rty::WKVid, rty::Binder<rty::Expr>>,
}

impl TypeFolder for WKVarSubst {
    fn fold_expr(&mut self, e: &rty::Expr) -> rty::Expr {
        match e.kind() {
            rty::ExprKind::WKVar(wkvar @ rty::WKVar { wkvid, .. })
                if let Some(bound_e) = self.wkvar_instantiations.get(wkvid) =>
            {
                // The bound expression has bound vars that need to be replaced
                // by the args given to the wkvar (in order).
                let instantiated_e = bound_e.replace_bound_refts(&wkvar.args);
                // NOTE: keeps the original wkvar to allow iterative
                // substitutions --- it gets turned into TRUE when output
                // anyway.
                rty::Expr::and(instantiated_e, e.clone())
            }
            _ => e.super_fold_with(self),
        }
    }
}

struct ProductEtaExpander<'a> {
    // An expression that evalutes to the current_expr
    current_path: rty::Expr,
    // Maps an interior part of the product to its eta expansion.
    expr_to_eta_expansion: &'a mut HashMap<rty::Expr, rty::Expr>,
}

impl TypeVisitor for ProductEtaExpander<'_> {
    fn visit_expr(&mut self, expr: &rty::Expr) -> ControlFlow<Self::BreakTy> {
        match expr.kind() {
            rty::ExprKind::Tuple(subexprs) | rty::ExprKind::Ctor(_, subexprs) => {
                let current_path = self.current_path.clone();
                let mk_proj = |field| {
                    if let rty::ExprKind::Ctor(ctor, _) = expr.kind() {
                        rty::FieldProj::Adt { def_id: ctor.def_id(), field }
                    } else {
                        rty::FieldProj::Tuple { arity: subexprs.len(), field }
                    }
                };
                for (i, subexpr) in subexprs.iter().enumerate() {
                    self.current_path = rty::Expr::field_proj(&current_path, mk_proj(i as u32));
                    subexpr.visit_with(self)?;
                }
                ControlFlow::Continue(())
            }
            _ => {
                // NOTE: in theory this should be appending to a vec, not
                // clobbering whatever lives at expr currently. But we don't
                // currently support making multiple solutions in the weak kvar
                // instantiation so I'm not bothering.
                self.expr_to_eta_expansion
                    .insert(expr.clone(), self.current_path.clone());
                ControlFlow::Continue(())
            }
        }
    }
}

/// Recursively "unpacks" a product by eta-expanding each part of it.
/// Maps each part of the product to its eta-expanded path.
///
/// e.g.
///
///     in = {
///       current_path: self,
///       expr: TwoFields { 0: (a0.0, a0.1), 1: 42 })
///     }
///
///     out =
///       a0.0 => self.0.0
///       a0.1 => self.0.1
///       42 => self.1
impl<'a> ProductEtaExpander<'a> {
    fn eta_expand_products(
        current_path: rty::Expr,
        expr: rty::Expr,
        expr_to_eta_expansion: &'a mut HashMap<rty::Expr, rty::Expr>,
    ) {
        let mut expander = ProductEtaExpander { current_path, expr_to_eta_expansion };
        let _ = expr.visit_with(&mut expander);
    }
}

#[derive(Clone)]
pub struct WKVarSolutions {
    /// Each Expr is part of a conjunction of the solution.
    pub solutions: FxIndexMap<rty::WKVid, WKVarSolution>,
    pub num_nontrivial_head_cstrs: usize,
    /// All wkvars
    pub wkvars: FxIndexSet<rty::WKVid>,
    /// All wkvars that could be kvars
    pub internal_wkvars: FxHashSet<rty::WKVid>,
}

/// NOTE: we expect that the binders for `solved_exprs` and `assumed_exprs` are
/// in the same order, though it is likely (and probable) that the names differ.
/// We at least will check that the number of variables matches.
#[derive(Clone)]
pub struct WKVarSolution {
    /// Exprs we solved using our analysis (in a conjunction)
    pub solved_exprs: Option<rty::Binder<FxIndexSet<rty::Expr>>>,
    /// Exprs we assumed (this only happens when we cannot
    /// solve _any_ wkvar --- we'll assume a solution to
    /// try and make everything work), also in a conjunction
    pub assumed_exprs: Option<rty::Binder<FxIndexSet<rty::Expr>>>,
    /// Expressions removed from the `solved_exprs`. Given without
    /// a binder because we assume them to be compatible.
    pub removed_solved_exprs: FxHashSet<rty::Expr>,
    pub actual_exprs: Vec<rty::Binder<rty::Expr>>,
}

impl WKVarSolution {
    pub fn empty(genv: GlobalEnv, wkvid: rty::WKVid) -> Self {
        let actual_exprs;
        if let Some(solutions_map) = &genv.weak_kvars_for(wkvid.0) {
            if let Some(sols) = solutions_map.get(&wkvid.1.as_u32()) {
                actual_exprs = sols.clone();
            } else {
                actual_exprs = vec![];
            }
        } else {
            actual_exprs = vec![];
        }

        Self {
            solved_exprs: Default::default(),
            assumed_exprs: Default::default(),
            removed_solved_exprs: Default::default(),
            actual_exprs,
        }
    }
    pub fn into_wkvar_subst(&self) -> Option<rty::Binder<rty::Expr>> {
        match (&self.solved_exprs, &self.assumed_exprs) {
            (None, Some(assumed_exprs)) => {
                Some(assumed_exprs.map_ref(|exprs| rty::Expr::and_from_iter(exprs.iter().cloned())))
            }
            (Some(solved_exprs), None) => {
                Some(solved_exprs.map_ref(|exprs| {
                    rty::Expr::and_from_iter(
                        exprs
                            .iter()
                            .filter(|expr| !self.removed_solved_exprs.contains(expr))
                            .cloned(),
                    )
                }))
            }
            (None, None) => None,
            (Some(solved_exprs), Some(assumed_exprs)) => {
                // The best we can do is just check the # of vars matches
                // since we can't reasonably expect the names to be the same
                assert!(solved_exprs.vars().len() == assumed_exprs.vars().len());
                Some(assumed_exprs.map_ref(|assumed_exprs_inner| {
                    // Put all of the solutions into a conjunction
                    rty::Expr::and_from_iter(
                        assumed_exprs_inner.iter().cloned().chain(
                            solved_exprs
                                .skip_binder_ref()
                                .iter()
                                .filter(|expr| !self.removed_solved_exprs.contains(expr))
                                .cloned(),
                        ),
                    )
                }))
            }
        }
    }

    fn has_solved_expr(&self, expr: &rty::Expr) -> bool {
        let in_solved_exprs = self
            .solved_exprs
            .as_ref()
            .map(|solved_exprs| {
                solved_exprs
                    .skip_binder_ref()
                    .contains(&expr.erase_metadata())
            })
            .unwrap_or(false);
        let in_assumed_exprs = self
            .assumed_exprs
            .as_ref()
            .map(|assumed_exprs| {
                assumed_exprs
                    .skip_binder_ref()
                    .contains(&expr.erase_metadata())
            })
            .unwrap_or(false);
        in_solved_exprs || in_assumed_exprs
    }

    fn add_expr(
        opt_exprs: &mut Option<rty::Binder<FxIndexSet<rty::Expr>>>,
        expr: &rty::Binder<rty::Expr>,
    ) -> bool {
        if let Some(exprs) = opt_exprs {
            assert!(exprs.vars() == expr.vars());
            exprs
                .skip_binder_ref_mut()
                .insert(expr.skip_binder_ref().erase_metadata())
        } else {
            *opt_exprs = Some(expr.map_ref(|inner_expr| {
                let mut set = FxIndexSet::default();
                set.insert(inner_expr.erase_metadata());
                set
            }));
            true
        }
    }

    fn add_solved_expr(&mut self, solved_expr: &rty::Binder<rty::Expr>) -> bool {
        if self
            .removed_solved_exprs
            .contains(&solved_expr.skip_binder_ref().erase_metadata())
        {
            return false;
        }
        Self::add_expr(&mut self.solved_exprs, solved_expr)
    }

    fn add_assumed_expr(&mut self, assumed_expr: &rty::Binder<rty::Expr>) -> bool {
        if self
            .solved_exprs
            .as_ref()
            .map(|solved_exprs| {
                solved_exprs
                    .skip_binder_ref()
                    .contains(&assumed_expr.skip_binder_ref().erase_metadata())
            })
            .unwrap_or(false)
        {
            return false;
        }
        Self::add_expr(&mut self.assumed_exprs, assumed_expr)
    }

    fn add_actual_exprs(&mut self, actual_exprs: &Vec<rty::Binder<rty::Expr>>) {
        self.actual_exprs = actual_exprs.clone();
    }

    fn remove_solved_expr(
        &mut self,
        annotated_solution: &Option<&Vec<rty::Binder<rty::Expr>>>,
    ) -> bool {
        if let Some(solved_exprs) = &self.solved_exprs {
            let mut exprs_to_remove = solved_exprs.skip_binder_ref().iter().filter(|solved_expr| {
                // Is the solved_expr in any of the annotated solutions?
                // If so, don't remove it.
                if let Some(annotated_solution) = annotated_solution {
                    !annotated_solution.iter().any(|annotated_expr| {
                        annotated_expr.skip_binder_ref().erase_metadata().kind()
                            == solved_expr.kind()
                    })
                } else {
                    true
                }
            });
            for expr_to_remove in exprs_to_remove {
                // Make sure we haven't added it already
                if self.removed_solved_exprs.insert(expr_to_remove.clone()) {
                    return true;
                }
            }
        }
        false
    }

    pub fn to_summary(&self, genv: GlobalEnv) -> WKVarSolutionSummary {
        let pretty_cx = flux_middle::pretty::PrettyCx::default(genv);
        let summary_solved_exprs = if let Some(solved_exprs) = &self.solved_exprs {
            let binder_vars = solved_exprs.vars();
            solved_exprs
                .skip_binder_ref()
                .iter()
                .flat_map(|expr| {
                    if !self.removed_solved_exprs.contains(expr) {
                        let binder = rty::Binder::bind_with_vars(expr.clone(), binder_vars.clone());
                        Some(format!("{:?}", flux_middle::pretty::with_cx!(&pretty_cx, &binder)))
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            vec![]
        };
        let summary_assumed_exprs = if let Some(assumed_exprs) = &self.assumed_exprs {
            let binder_vars = assumed_exprs.vars();
            assumed_exprs
                .skip_binder_ref()
                .iter()
                .map(|expr| {
                    let binder = rty::Binder::bind_with_vars(expr.clone(), binder_vars.clone());
                    format!("{:?}", flux_middle::pretty::with_cx!(&pretty_cx, &binder))
                })
                .collect()
        } else {
            vec![]
        };
        let summary_removed_solved_exprs = self
            .removed_solved_exprs
            .iter()
            .map(|expr| format!("{:?}", flux_middle::pretty::with_cx!(&pretty_cx, &expr)))
            .collect_vec();
        let summary_actual_exprs = self
            .actual_exprs
            .iter()
            .map(|expr| format!("{:?}", flux_middle::pretty::with_cx!(&pretty_cx, &expr)))
            .collect_vec();
        WKVarSolutionSummary {
            solved_exprs: summary_solved_exprs,
            assumed_exprs: summary_assumed_exprs,
            removed_solved_exprs: summary_removed_solved_exprs,
            actual_exprs: summary_actual_exprs,
        }
    }
}

#[derive(Clone, serde::Serialize)]
pub struct WKVarSolutionSummary {
    pub solved_exprs: Vec<String>,
    pub assumed_exprs: Vec<String>,
    pub removed_solved_exprs: Vec<String>,
    pub actual_exprs: Vec<String>,
}

impl WKVarSolutionSummary {
    pub fn to_stats(&self) -> WKVarSolutionStats {
        WKVarSolutionStats {
            num_solved_exprs: self.solved_exprs.len(),
            num_assumed_exprs: self.assumed_exprs.len(),
            num_removed_solved_exprs: self.removed_solved_exprs.len(),
            num_actual_exprs: self.actual_exprs.len(),
        }
    }
}

#[derive(serde::Serialize, Default)]
pub struct WKVarSolutionStats {
    pub num_solved_exprs: usize,
    pub num_assumed_exprs: usize,
    pub num_removed_solved_exprs: usize,
    pub num_actual_exprs: usize,
}

impl WKVarSolutionStats {
    pub fn combine(&self, other: &Self) -> Self {
        Self {
            num_solved_exprs: self.num_solved_exprs + other.num_solved_exprs,
            num_assumed_exprs: self.num_assumed_exprs + other.num_assumed_exprs,
            num_removed_solved_exprs: self.num_removed_solved_exprs
                + other.num_removed_solved_exprs,
            num_actual_exprs: self.num_actual_exprs + other.num_actual_exprs,
        }
    }
}

impl WKVarSolutions {
    pub fn new(
        genv: GlobalEnv,
        num_nontrivial_head_cstrs: usize,
        wkvars: FxIndexSet<rty::WKVid>,
        internal_wkvars: FxHashSet<rty::WKVid>,
    ) -> Self {
        // Initialize the solutions with all of the wkvars.
        let solutions = wkvars
            .iter()
            .chain(internal_wkvars.iter())
            .map(|wkvid| {
                (*wkvid, WKVarSolution::empty(genv, *wkvid))
            })
            .collect();
        Self { solutions, num_nontrivial_head_cstrs, wkvars, internal_wkvars }
    }

    pub fn write_summary_file(
        &self,
        genv: GlobalEnv,
        path: &std::path::PathBuf,
    ) -> std::io::Result<()> {
        let solutions_by_wkvar: HashMap<String, WKVarSolutionSummary> = self
            .solutions
            .iter()
            .map(|(wkvid, solution)| {
                let wkvar_key =
                    format!("{}::$wk{}", genv.tcx().def_path_str(wkvid.0), wkvid.1.as_u32());
                (wkvar_key, solution.to_summary(genv))
            })
            .collect();
        let file = std::fs::File::create(path.as_path())?;
        let mut writer = std::io::BufWriter::new(file);
        Ok(serde_json::to_writer_pretty(writer, &solutions_by_wkvar)?)
    }

    pub fn write_stats_file(
        &self,
        genv: GlobalEnv,
        path: &std::path::PathBuf,
    ) -> std::io::Result<()> {
        #[derive(serde::Serialize)]
        struct CsvRow {
            fn_name: String,
            num_solved_exprs: usize,
            num_assumed_exprs: usize,
            num_removed_solved_exprs: usize,
            num_actual_exprs: usize,
        }
        let mut stats_by_fn: HashMap<String, WKVarSolutionStats> = HashMap::default();
        let mut solutions_by_fn: HashMap<_, HashMap<rty::WKVid, rty::Binder<rty::Expr>>> = HashMap::default();
        let mut num_nontrivial_real_wkvars = 0;
        let mut num_nontrivial_internal_wkvars = 0;
        self.solutions.iter().for_each(|(wkvid, solution)| {
            if solution.actual_exprs.len() > 0 {
                if self.internal_wkvars.contains(&wkvid) {
                    num_nontrivial_internal_wkvars += 1;
                } else {
                    num_nontrivial_real_wkvars += 1;
                }
            }
            let wkvar_fn_name = genv.tcx().def_path_str(wkvid.0);
            if let Some(solved_exprs) = &solution.solved_exprs {
                let sol = solved_exprs.map_ref(|exprs| rty::Expr::and_from_iter(exprs.iter().cloned()));
                solutions_by_fn.entry(wkvid.0)
                               .or_default()
                               .insert(*wkvid, sol);
            }
            stats_by_fn
                .entry(wkvar_fn_name)
                .and_modify(|stats| {
                    *stats = stats.combine(&solution.to_summary(genv).to_stats());
                })
                .or_insert_with(|| solution.to_summary(genv).to_stats());
        });

        for (def_id, wkvar_instantiations) in solutions_by_fn {
            let wkvar_fn_name = genv.tcx().def_path_str(def_id);
            let fn_sig = genv.fn_sig(def_id).unwrap();
            let mut wkvar_subst = WKVarSubst { wkvar_instantiations };
            let solved_fn_sig = rty::EarlyBinder(fn_sig.skip_binder_ref().fold_with(&mut wkvar_subst));
            let fixed_fn_sig_snippet =
                format!("{:?}", pretty::with_cx!(&pretty::PrettyCx::default(genv), &solved_fn_sig));
            println!("Solution: fn {}", wkvar_fn_name);
            println!("  {}", fixed_fn_sig_snippet);
        }

        let mut writer = csv::Writer::from_path(path.as_path())?;
        let mut total = WKVarSolutionStats::default();
        let num_fns = stats_by_fn.len();
        let mut latex_table = String::new();
        latex_table.push_str("Function name & Inferences & Guided Assumptions & Guided Removals & Ground Truth Expressions \\\\\n");
        stats_by_fn.into_iter().try_for_each(|(fn_name, stats)| {
            total = total.combine(&stats);
            let row = CsvRow {
                fn_name,
                num_solved_exprs: stats.num_solved_exprs,
                num_assumed_exprs: stats.num_assumed_exprs,
                num_removed_solved_exprs: stats.num_removed_solved_exprs,
                num_actual_exprs: stats.num_actual_exprs,
            };
            println!("fn {}", row.fn_name);
            println!("  num solved:  {}", row.num_solved_exprs);
            println!("  num assumed: {}", row.num_assumed_exprs);
            println!("  num removed: {}", row.num_removed_solved_exprs);
            println!("  num actual:  {}", row.num_actual_exprs);
            latex_table.push_str(&format!("{} & {} & {} & {} & {}\\\\\n", row.fn_name, row.num_solved_exprs, row.num_assumed_exprs, row.num_removed_solved_exprs, row.num_actual_exprs));
            writer.serialize(row)
        })?;
        let num_wkvars = self.wkvars.len();
        let num_internal_wkvars = self.internal_wkvars.len();
        latex_table.push_str(&format!("TOTAL & {} & {} & {} & {}", total.num_solved_exprs, total.num_assumed_exprs, total.num_removed_solved_exprs, total.num_actual_exprs));
        println!("SUMMARY");
        println!("  num fns:                    {}", num_fns);
        println!("  num total wkvars:           {}", num_wkvars);
        println!("    internal wkvars:          {}", num_internal_wkvars);
        println!("    real wkvars:              {}", num_wkvars - num_internal_wkvars);
        println!(
            "  num nontrivial wkvars:      {}",
            num_nontrivial_real_wkvars + num_nontrivial_internal_wkvars
        );
        println!("    internal wkvars:          {}", num_nontrivial_internal_wkvars);
        println!("    real wkvars:              {}", num_nontrivial_real_wkvars);
        println!("  num nontrivial head cstrs:  {}", self.num_nontrivial_head_cstrs);
        println!("  num solved exprs:           {}", total.num_solved_exprs);
        println!("  num assumed exprs:          {}", total.num_assumed_exprs);
        println!("  num removed exprs:          {}", total.num_removed_solved_exprs);
        println!("  num actual exprs:           {}", total.num_actual_exprs);
        println!("Copy/pastable entry:");
        println!(
            "{}",
            [
                num_fns,
                num_wkvars,
                num_internal_wkvars,
                num_wkvars - num_internal_wkvars,
                num_nontrivial_real_wkvars + num_nontrivial_internal_wkvars,
                num_nontrivial_internal_wkvars,
                num_nontrivial_real_wkvars,
                self.num_nontrivial_head_cstrs,
                total.num_solved_exprs,
                total.num_assumed_exprs,
                total.num_removed_solved_exprs,
                total.num_actual_exprs
            ]
            .iter()
            .map(|n| format!("{}", n))
            .join("\t")
        );
        println!("LaTeX Table:\n{}", latex_table);
        let total_row = CsvRow {
            fn_name: "TOTAL".to_string(),
            num_solved_exprs: total.num_solved_exprs,
            num_assumed_exprs: total.num_assumed_exprs,
            num_removed_solved_exprs: total.num_removed_solved_exprs,
            num_actual_exprs: total.num_actual_exprs,
        };
        writer.serialize(total_row)?;
        writer.flush()?;

        Ok(())
    }

    fn prompt_user(&mut self, genv: GlobalEnv, prev_interactions: &mut Vec<String>, file_read_user_interactions: &mut Option<Vec<String>>) -> bool {
        enum InteractionKind {
            AddGroundTruth(rty::Binder<rty::Expr>),
            RemoveSolution(rty::Expr),
        };
        struct UserInteraction {
            wkvid: rty::WKVid,
            kind: InteractionKind,
        }
        // Step 1: Group wkvars into functions
        let mut wkvars_by_fn: FxIndexMap<DefId, Vec<rty::KVid>> = FxIndexMap::default();
        for wkvid in self.solutions.keys() {
            wkvars_by_fn.entry(wkvid.0)
                .and_modify(|kvids| kvids.push(wkvid.1))
                .or_insert_with(|| vec![wkvid.1]);
        }
        for kvids in wkvars_by_fn.values_mut() {
            kvids.sort_by_key(|kvid| kvid.as_u32());
        }
        // Step 2: Assign each user interaction an id
        let alphas = 'a'..='z';
        let single_alpha_ids = alphas.clone().map(|a| a.to_string());
        let double_alpha_ids = iproduct!(alphas.clone(), alphas).map(|(a1, a2)| format!("{}{}", a1, a2));
        let mut id_prefix = single_alpha_ids.chain(double_alpha_ids);
        let mut interactions: FxIndexMap<String, UserInteraction> = FxIndexMap::default();
        let mut wkvar_subst = WKVarSubst {
            wkvar_instantiations:
                    self
                        .solutions
                        .iter()
                        .filter_map(|(wkvid, solution)| solution.into_wkvar_subst().map(|subst| (wkvid.clone(), subst)))
                        .collect()
        };
        let fn_pretty_cx = pretty::PrettyCx::default(genv).hide_regions(true);
        for (fn_def_id, kvids) in wkvars_by_fn.iter() {
            if file_read_user_interactions.is_none() {
                let fn_name = genv.tcx().def_path_str(fn_def_id);
                println!("fn {}", fn_name);
                let fn_sig = genv.fn_sig(fn_def_id).unwrap();
                let solved_fn_sig = rty::EarlyBinder(fn_sig.skip_binder_ref().fold_with(&mut wkvar_subst));
                println!("sig {:?}", pretty::with_cx!(&fn_pretty_cx, &solved_fn_sig));
            }
            for kvid in kvids {
                let wkvid = (*fn_def_id, *kvid);
                if file_read_user_interactions.is_none() {
                    println!("  $wk{}", kvid.as_u32());
                }
                let solution = &self.solutions[&wkvid];
                let ground_truth_exprs = solution.actual_exprs.iter()
                                                        .filter(|expr| !expr.skip_binder_ref().is_trivially_true()
                                                                && !solution.assumed_exprs
                                                                            .as_ref()
                                                                            .map(|assumed_exprs| assumed_exprs.skip_binder_ref()
                                                                                 .contains(expr.skip_binder_ref()))
                                                                            .unwrap_or(false)
                                                        )
                                                        .cloned()
                                                        .collect_vec();
                if !ground_truth_exprs.is_empty() {
                    if file_read_user_interactions.is_none() {
                        println!("    Add a ground truth solution?");
                    }
                    for expr in ground_truth_exprs {
                        let id = format!("g{}", id_prefix.next().unwrap());
                        if file_read_user_interactions.is_none() {
                            println!("    [{}] {:?}", id, &expr);
                        }
                        let interaction = UserInteraction {
                            wkvid: (*fn_def_id, *kvid),
                            kind: InteractionKind::AddGroundTruth(expr),
                        };
                        interactions.insert(id, interaction);
                    }
                }
                if let Some(solved_exprs) = &solution.solved_exprs && !solved_exprs.skip_binder_ref().is_empty() {
                    if file_read_user_interactions.is_none() {
                        println!("    Remove an assumed solution?");
                    }
                    for expr in solved_exprs.skip_binder_ref() {
                        // Don't try to double remove
                        if solution.removed_solved_exprs.contains(expr) {
                            continue;
                        }
                        let id = format!("r{}", id_prefix.next().unwrap());
                        if file_read_user_interactions.is_none() {
                            println!("    [{}] {:?}", id, expr);
                        }
                        let interaction = UserInteraction {
                            wkvid: (*fn_def_id, *kvid),
                            kind: InteractionKind::RemoveSolution(expr.clone()),
                        };
                        interactions.insert(id, interaction);
                    }
                }
            }
        }
        let mut input_ok = false;
        let mut input = String::new();
        let mut user_inputs = vec![];
        while !input_ok {
            if file_read_user_interactions.is_none() {
                println!("Enter your choices separated by commas");
            }
            input.clear();
            match file_read_user_interactions {
                Some(interactions) => {
                    // Read from the file
                    // (will panic if the file doesn't have enough interactions)
                    input = interactions.remove(0);
                }
                None => {
                    std::io::stdin().read_line(&mut input).unwrap();
                }
            }
            if input.is_empty() || input == "\n" {
                user_inputs = vec![];
                break;
            }
            match input.trim_end_matches("\n").split(",").map(|id| {
                interactions.get(id).ok_or_else(|| format!("Invalid ID: {}", id))
            }).try_collect() {
                Ok(inputs) => {
                    user_inputs = inputs;
                    input_ok = true;
                }
                Err(err) => println!("{}", err),
            }
        }
        prev_interactions.push(input.trim_end_matches("\n").to_string());

        let mut any_interaction = false;
        for interaction in user_inputs {
            let solution = &mut self.solutions[&interaction.wkvid];
            match &interaction.kind {
                InteractionKind::AddGroundTruth(expr) => {
                    println!("Adding ground truth {:?} to {:?}", expr, interaction.wkvid);
                    any_interaction = solution.add_assumed_expr(&expr) || any_interaction;
                }
                InteractionKind::RemoveSolution(expr) => {
                    println!("Removing {:?} from {:?}", expr, interaction.wkvid);
                    any_interaction = solution.removed_solved_exprs.insert(expr.clone()) || any_interaction;
                }
            }
        }
        any_interaction
    }
}

pub struct Constraint {
    pub def_id: MaybeExternId,
    pub refine_tree: RefineTree,
    pub kvgen: KVarGen,
    pub query_kind: FixpointQueryKind,
    pub scrape_quals: bool,
    pub backend: SmtSolver,
}

pub type Constraints = Vec<Constraint>;

pub fn iterative_solve<F>(
    genv: GlobalEnv,
    cstrs: Constraints,
    max_iters: usize,
    report_errors: F,
) -> QueryResult<(WKVarSolutions, Vec<(LocalDefId, Vec<FixpointCheckError<Tag>>)>, Vec<String>)>
    where F: Fn(LocalDefId, Vec<FixpointCheckError<Tag>>)
{
    let mut constraint_lhs_wkvars: FxIndexMap<LocalDefId, FxIndexSet<rty::WKVid>> =
        FxIndexMap::default();
    let mut constraint_rhs_wkvars: FxIndexMap<LocalDefId, FxIndexSet<rty::WKVid>> =
        FxIndexMap::default();
    let mut num_nontrivial_head_cstrs = 0;
    for cstr in &cstrs {
        let id = cstr.def_id.expect_local();
        let (lhs_wkvars, rhs_wkvars) = cstr.refine_tree.wkvars();
        num_nontrivial_head_cstrs += cstr.refine_tree.num_nontrivial_head_cstrs();
        // println!("all LHS wkvars for {:?}: {:?}", id, lhs_wkvars.iter().collect_vec());
        // println!("all RHS wkvars for {:?}: {:?}", id, rhs_wkvars.iter().collect_vec());
        constraint_rhs_wkvars.insert(id, rhs_wkvars.into_iter().collect());
        constraint_lhs_wkvars.insert(id, lhs_wkvars.into_iter().collect());
    }
    let lhs_wkvars: FxHashSet<rty::WKVid> =
        constraint_lhs_wkvars.values().flatten().cloned().collect();
    let rhs_wkvars: FxHashSet<rty::WKVid> =
        constraint_rhs_wkvars.values().flatten().cloned().collect();
    let wkvars = lhs_wkvars.union(&rhs_wkvars).cloned().collect();
    // These are the solutions for the current pass.
    //
    // It is more stable to go "breadth-first" and collect the wkvar solutions
    // for all separate constraints, rather than accumulating them as we go
    // through each constraint.
    let mut curr_solutions = WKVarSolutions::new(genv, num_nontrivial_head_cstrs, wkvars, rhs_wkvars);
    let mut new_solutions = curr_solutions.clone();
    let mut any_wkvar_change = true;
    let mut i = 1;
    let mut all_errors = Vec::new();
    let mut user_interactions = Vec::new();
    let mut file_read_user_interactions = if let Some(interactions_file) = flux_config::user_interactions_file() {
        let interactions = std::fs::read_to_string(interactions_file.as_path()).unwrap().lines().map(|line| line.to_string()).collect_vec();
        println!("Read user interactions from file:\n  {:?}", interactions);
        Some(interactions)
    } else {
        None
    };
    while any_wkvar_change && i <= max_iters {
        println!("iteration {} of {}", i, max_iters);
        any_wkvar_change = false;
        all_errors = Vec::new();
        for cstr in &cstrs {
            let mut fcx = FixpointCtxt::new(genv, cstr.def_id, cstr.kvgen.clone());

            let mut wkvar_subst = WKVarSubst {
                // These solutions correspond to the solutions we got LAST
                // iteration (emtpy for iteration 1). This is to prevent any
                // solutions from this iteration affecting the results.
                //
                // When we run flux, we don't report only the first failing
                // constraint, but all of them.
                wkvar_instantiations: curr_solutions
                    .solutions
                    .iter()
                    .filter_map(|(wkvid, solution)| solution.into_wkvar_subst().map(|subst| (wkvid.clone(), subst)))
                    .collect(),
            };
            // if solutions.solutions.len() > 0 {
            //     println!("{:?}", cstr.refine_tree);
            // }
            let mut solved_refine_tree = cstr.refine_tree.fold_with(&mut wkvar_subst);
            // if solutions.solutions.len() > 0 {
            //     println!("solved\n{:?}", solved_refine_tree);
            // }
            solved_refine_tree.simplify(genv);
            let fcstr = solved_refine_tree.into_fixpoint(&mut fcx)?;
            // println!("converted to fixpoint");
            let fixpoint_answer = fcx.check(
                &mut QueryCache::new(),
                cstr.def_id,
                fcstr,
                cstr.query_kind,
                cstr.scrape_quals,
                cstr.backend,
            )?;
            for error in &fixpoint_answer.errors {
                // println!("failing constraint {:?}", &error.blame_ctx.expr);
                // let solution_candidates = _find_solution_candidates(&error.blame_ctx);
                for (wkvid, instantiations) in error.possible_solutions.iter() {
                    for instantiation in instantiations {
                        // // Accept all solutions given
                        // let ground_truth_solutions = {
                        //     if let Some(solutions_map) = genv.weak_kvars_for(wkvid.0) {
                        //         solutions_map
                        //             .get(&wkvid.1.as_u32())
                        //             .cloned()
                        //             .unwrap_or(vec![])
                        //     } else {
                        //         vec![]
                        //     }
                        // };
                        println!("Adding an instantiation for wkvar {:?}:", wkvid);
                        println!("  {:?}", instantiation);
                        // Record the solution in the NEW solutions, so that
                        // subsequent constraints aren't checked against it.
                        let solution = &mut new_solutions
                            .solutions.get_mut(wkvid)
                            .unwrap();
                            // .or_insert_with(|| WKVarSolution::empty(genv, *wkvid));
                        // // HACK: so that we don't waste time running around in circles, we
                        // // will not attempt to add a wkvar instantiation if:
                        // //   1. All of the ground truth solutions are
                        // //      present in the solution.
                        // //   2. There is at least 1 ground truth solution OR
                        // //      we have removed at least 1 spurious
                        // //      solution.  The latter case is to prevent us
                        // //      adding and then removing different spurious
                        // //      solutions over and over again.
                        // if ground_truth_solutions
                        //     .iter()
                        //     .all(|sol| solution.has_solved_expr(sol.skip_binder_ref()))
                        //     && (ground_truth_solutions.len() > 0
                        //         || solution.removed_solved_exprs.len() > 0)
                        // {
                        //     println!("skipping adding an expr because of reasons");
                        //     continue;
                        // }
                        any_wkvar_change = solution.add_solved_expr(instantiation) || any_wkvar_change;
                    }
                }
            }
            let local_id = cstr.def_id.expect_local();
            if !fixpoint_answer.errors.is_empty() {
                all_errors.push((local_id, fixpoint_answer.errors));
            }
        }
        // Early exit if there are no errors to process.
        //
        // Before we would just rely on `any_wkvar_change` and exit if there
        // were no more changes, but now we have logic that will try to reveal
        // wkvars which we should only do if there are no more errors.
        if all_errors.is_empty() {
            break;
        }
        i += 1;

        if !any_wkvar_change {
            for (local_id, err) in &all_errors {
                report_errors(*local_id, err.clone());
            }
            any_wkvar_change = any_wkvar_change || new_solutions.prompt_user(genv, &mut user_interactions, &mut file_read_user_interactions);
        }

        // Now put the new solutions into the current solutions,
        // we will use them for the next iterations.
        curr_solutions = new_solutions.clone();

        // COMMENTED OUT: auto solving logic. Replaced with prompting for input.
        //
        // // Our analysis cannot solve _any_ wkvars, so we will try to continue by
        // // "revealing" one of the correct solutions.
        // //
        // // If our analysis cannot solve a wkvar because there are no more
        // // errors, this won't change anything (because the errors list will be
        // // empty).
        // // if !any_wkvar_change {
        //     println!("No changes: trying to add a wkvar solution");
        //     'outer: for (local_id, errs) in &all_errors {
        //         for err in errs {
        //             for wkvar in &err.blame_ctx.blame_analysis.wkvars {
        //                 // println!("Trying {:?} for {:?}", wkvar.wkvid, local_id);
        //                 if let Some(solutions_map) = &genv.weak_kvars_for(wkvar.wkvid.0) {
        //                     if let Some(sols) = solutions_map.get(&wkvar.wkvid.1.as_u32()) {
        //                         // println!("There are some solutions, trying them...");
        //                         for sol in sols {
        //                             let current_sol = curr_solutions
        //                                 .solutions
        //                                 .entry(wkvar.wkvid)
        //                                 .or_insert_with(|| WKVarSolution::empty(genv, wkvar.wkvid));
        //                             any_wkvar_change = current_sol.add_assumed_expr(sol);
        //                             if any_wkvar_change {
        //                                 println!(
        //                                     "assumed solution {:?} for wkvar {:?}",
        //                                     sol, wkvar
        //                                 );
        //                                 break 'outer;
        //                             }
        //                         }
        //                     }
        //                 }
        //             }
        //         }
        //     }
        // }
        // // If we can't reveal _any_ wkvar that directly relates to a constraint,
        // // we will instead try to reveal a wkvar used in the function itself.
        // if !any_wkvar_change {
        //     println!(
        //         "Still no changes: trying to add a wkvar solution anywhere in the failing functions"
        //     );
        //     'outer: for (local_id, _errs) in &all_errors {
        //         for wkvid in &constraint_lhs_wkvars[local_id] {
        //             // println!("Trying {:?} for {:?}", wkvid, local_id);
        //             if let Some(solutions_map) = &genv.weak_kvars_for(wkvid.0) {
        //                 if let Some(sols) = solutions_map.get(&wkvid.1.as_u32()) {
        //                     // println!("There are some solutions, trying them...");
        //                     for sol in sols {
        //                         let current_sol = curr_solutions
        //                             .solutions
        //                             .entry(*wkvid)
        //                             .or_insert_with(|| WKVarSolution::empty(genv, *wkvid));
        //                         any_wkvar_change = current_sol.add_assumed_expr(sol);
        //                         if any_wkvar_change {
        //                             println!("assumed solution {:?} for wkvid {:?}", sol, wkvid);
        //                             break 'outer;
        //                         }
        //                     }
        //                 }
        //             }
        //         }
        //     }
        // }
        // // If we still haven't gotten any changes, start to remove spurious
        // // constraints from the solutions
        // if !any_wkvar_change {
        //     println!("Still no changes: trying to remove wkvar solutions");
        //     'outer: for (local_id, _errs) in &all_errors {
        //         for wkvid in &constraint_rhs_wkvars[local_id] {
        //             // println!("Trying {:?} for {:?}", wkvid, local_id);
        //             if let Some(solution) = curr_solutions.solutions.get_mut(wkvid) {
        //                 match &genv.weak_kvars_for(wkvid.0) {
        //                     Some(solutions_map) => {
        //                         let current_solutions = solutions_map.get(&wkvid.1.as_u32());
        //                         any_wkvar_change = solution.remove_solved_expr(&current_solutions);
        //                     }
        //                     None => {
        //                         any_wkvar_change = solution.remove_solved_expr(&None);
        //                     }
        //                 }
        //                 if any_wkvar_change {
        //                     println!("Removed a part of a wkvar solution, continuing...");
        //                     break 'outer;
        //                 }
        //             }
        //         }
        //     }
        // }
        // i += 1;
    }
    Ok((new_solutions, all_errors, user_interactions))
}

/// DEPRECATED: Solution candidates are now generated by doing qe and are no
/// longer a part of the BlameCtxt.
///
/// Heuristic and syntactic approach to finding candidates each of whose proof
/// entails the failing constraint (blame_ctx.expr).
///
/// So far this is just the expression itself (trivial entailment) and
/// the equalities arising from antiunifying the expression with an
/// assumed predicate.
///
/// e.g. if the expression is x < y
///
/// assumed_pred: a < y
/// solution candidate: a == x
///
/// assumed_pred: a < b
/// solution candidate: a == x /\ b == y
///
/// assumed_pred: a > b
/// solution candidate: none
/// (it would be --- at the most conservative level taking into account these
///  are booleans --- a > b => x < y which is probably too trivial a constraint
///  to offer; we only equalities anyway)
pub fn _find_solution_candidates(blame_ctx: &BlameCtxt) -> Vec<rty::Expr> {
    // println!("Failing constraint: {:?}", &blame_ctx.expr);
    let mut candidates = vec![blame_ctx.expr.clone()];
    for assumed_pred in &blame_ctx.blame_analysis.assumed_preds {
        // println!("Trying to unify against pred {:?}", assumed_pred);
        let au_map = rty::anti_unify(&blame_ctx.expr, assumed_pred);
        // This checks if the antiunification is trivial, i.e.
        // blame_ctx.expr == assumed_pred
        if au_map.get(&blame_ctx.expr).is_some() {
            continue;
        }
        for (e1, e2) in au_map.iter() {
            match (e1.kind(), e2.kind()) {
                // (rty::ExprKind::Constant(..), _) => continue,
                // (_, rty::ExprKind::Constant(..)) => continue,
                // _ => {},
                (rty::ExprKind::Var(..), rty::ExprKind::Var(..)) => {}
                _ => continue,
            }
        }
        // build a conjunction of equalities between each au pair.
        let conjs = au_map.into_iter().flat_map(|(e1, e2)| {
            match (e1.kind(), e2.kind()) {
                (rty::ExprKind::Constant(..), _) | (_, rty::ExprKind::Constant(..)) => return None,
                _ => {}
                // (rty::ExprKind::Var(..), rty::ExprKind::Var(..)) => {},
                // _ => return None,
            }
            Some(rty::Expr::eq(e1, e2))
        });
        candidates.push(rty::Expr::and_from_iter(conjs));
    }
    candidates.retain_mut(|expr| {
        expr.simplify(&SnapshotMap::default());
        !(expr.is_trivially_false() || expr.is_trivially_true())
    });
    // for candidate in &candidates {
    //     println!("equality candidate: {:?}", candidate);
    // }
    return candidates;
}
