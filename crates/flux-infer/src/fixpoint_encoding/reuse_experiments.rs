//! Diagnostic-only experiments. No result here participates in acceptance.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Write,
    path::PathBuf,
    time::Instant,
};

use liquid_fixpoint::solution_validator::{Formula, Prepared, check_formulas, encode_formula};
use serde_json::{Value, json};

use super::*;

#[derive(Clone, Serialize, Deserialize)]
struct Slot {
    fingerprint: String,
    role: String,
    formula: Formula,
}
#[derive(Serialize, Deserialize)]
struct Observation {
    version: u32,
    task_key: String,
    hash: u64,
    safe: Option<bool>,
    slots: BTreeMap<String, Slot>,
    coverage: Vec<String>,
    result: Option<VerificationResult<TagIdx>>,
    prepared: Option<Prepared>,
    clause_results: Vec<String>,
}
pub(super) struct ExperimentRun {
    state_path: PathBuf,
    record: Value,
    slots: BTreeMap<String, Slot>,
    coverage: Vec<String>,
}

fn outcome(statuses: &[String]) -> &'static str {
    if statuses.iter().any(|s| s == "rejected") {
        "candidate_rejected"
    } else if statuses.iter().any(|s| s != "valid") {
        "inconclusive"
    } else {
        "predict_pass"
    }
}
fn timed(name: &str, f: impl FnOnce() -> Result<Value, String>) -> Value {
    let start = Instant::now();
    let mut result = f().unwrap_or_else(|reason| json!({"outcome":if reason.starts_with("z3_") || reason == "timeout" {"inconclusive"} else {"unavailable"}, "reason":reason}));
    result["name"] = name.into();
    result["total_ms"] = (start.elapsed().as_secs_f64() * 1000.0).into();
    result
}

impl<Tag: Hash + Eq + Copy> FixpointCtxt<'_, '_, Tag> {
    pub(crate) fn log_trivial_reuse_query(&mut self, def_id: DefId, kind: FixpointQueryKind) {
        let start = Instant::now();
        let key = kind.task_key(self.genv.tcx(), def_id);
        let crate_name = self
            .genv
            .tcx()
            .crate_name(rustc_hir::def_id::LOCAL_CRATE)
            .to_string();
        let (slots, mut coverage) = self.reuse_slots();
        let own_slot = format!("{}::wk0", self.genv.tcx().def_path_str(def_id));
        if rty::vc_skeleton::tracking_status(&own_slot) != "aligned" {
            coverage.push(format!("own_signature:{own_slot}"));
        }
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        use std::hash::Hasher;
        (crate_name.as_str(), key.as_str()).hash(&mut hasher);
        let path =
            config::vc_reuse_state().join(format!("{crate_name}-{:016x}.json", hasher.finish()));
        let observation = Observation {
            version: 1,
            task_key: key.clone(),
            hash: 0,
            safe: Some(true),
            slots,
            coverage: coverage.clone(),
            result: None,
            prepared: None,
            clause_results: vec![],
        };
        let record = json!({"schema_version":1,"crate":crate_name,"task_key":key,"change_category":"not_evaluated","coverage":coverage,"experiments":[],"reference":{"path":"trivial","safe":true,"fixpoint_ms":null,"cached_equivalent":true},"disagreements":[],"shared_preparation_ms":start.elapsed().as_secs_f64()*1000.0});
        let write = || -> Result<(), Box<dyn std::error::Error>> {
            fs::create_dir_all(config::vc_reuse_state())?;
            fs::write(path, serde_json::to_vec(&observation)?)?;
            fs::create_dir_all(config::log_dir())?;
            let mut file = fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(config::log_dir().join(format!("{crate_name}-vc-reuse-experiments.jsonl")))?;
            serde_json::to_writer(&mut file, &record)?;
            writeln!(file)?;
            Ok(())
        };
        if let Err(e) = write() {
            eprintln!("VC reuse trivial diagnostic output failed: {e}");
        }
    }
    fn reuse_slots(&mut self) -> (BTreeMap<String, Slot>, Vec<String>) {
        let mut slots = BTreeMap::new();
        let mut unavailable = vec![];
        for (key, role) in self.reuse_roles.clone() {
            if rty::vc_skeleton::tracking_status(&key) != "aligned" {
                unavailable.push(key);
                continue;
            }
            let Some((fingerprint, predicate)) = rty::vc_skeleton::experiment_slot(&key) else {
                unavailable.push(key);
                continue;
            };
            // Flatten product indices exactly as ordinary kvar generation does.
            // Reconstruct the product expression from independent scalar formals
            // before encoding, so no ADT selector is applied to an Int formal.
            let mut args = vec![];
            let mut params = vec![];
            let mut replacements = HashMap::new();
            let saved_fvars = self.ecx.local_var_env.fvars.clone();
            for kind in predicate.vars() {
                let root = self.ecx.local_var_env.fresh_name();
                let arg = rty::Expr::fvar(rty::Name::from_usize(root.index()));
                kind.expect_sort().walk(|sort, projections| {
                    let name = self.ecx.local_var_env.fresh_name();
                    let rname = rty::Name::from_usize(name.index());
                    self.ecx
                        .local_var_env
                        .insert_fvar_map(rname, NameProvenance::Unknown);
                    let encoded = self.ecx.local_var_env.fvars[&rname];
                    params.push((fixpoint::Var::Local(encoded), self.scx.sort_to_fixpoint(sort)));
                    replacements
                        .insert(rty::Expr::field_projs(&arg, projections), rty::Expr::fvar(rname));
                });
                args.push(arg);
            }
            let opened = predicate.replace_bound_refts(&args);
            struct Replace(HashMap<rty::Expr, rty::Expr>);
            impl rty::fold::TypeFolder for Replace {
                fn fold_expr(&mut self, e: &rty::Expr) -> rty::Expr {
                    use rty::fold::TypeSuperFoldable;
                    self.0
                        .get(&e.erase_metadata())
                        .cloned()
                        .unwrap_or_else(|| e.super_fold_with(self))
                }
            }
            use rty::fold::TypeFoldable;
            let opened = opened.fold_with(&mut Replace(replacements));
            use rty::fold::TypeVisitable;
            if opened
                .fvars()
                .iter()
                .any(|name| !self.ecx.local_var_env.fvars.contains_key(name))
            {
                self.ecx.local_var_env.fvars = saved_fvars;
                unavailable.push(format!("{key}:unflattened_product_argument"));
                continue;
            }
            let body = self.ecx.expr_to_fixpoint(&opened, &mut self.scx);
            self.ecx.local_var_env.fvars = saved_fvars;
            match body
                .map_err(|_| "slot_encoding".to_string())
                .and_then(|body| encode_formula(&params, &body))
            {
                Ok(formula) => {
                    slots.insert(key, Slot { fingerprint, role, formula });
                }
                Err(reason) => unavailable.push(format!("{key}:{reason}")),
            }
        }
        (slots, unavailable)
    }

    pub(super) fn start_reuse_experiments(
        &mut self,
        task: &fixpoint::Task,
        def_id: DefId,
        kind: FixpointQueryKind,
        evaluate: bool,
    ) -> ExperimentRun {
        let start = Instant::now();
        let key = kind.task_key(self.genv.tcx(), def_id);
        let crate_name = self
            .genv
            .tcx()
            .crate_name(rustc_hir::def_id::LOCAL_CRATE)
            .to_string();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        use std::hash::Hasher;
        (crate_name.as_str(), key.as_str()).hash(&mut hasher);
        let state_path =
            config::vc_reuse_state().join(format!("{crate_name}-{:016x}.json", hasher.finish()));
        let (slots, mut coverage) = self.reuse_slots();
        let own_slot = format!("{}::wk0", self.genv.tcx().def_path_str(def_id));
        if rty::vc_skeleton::tracking_status(&own_slot) != "aligned" {
            coverage.push(format!("own_signature:{own_slot}"));
        }
        let mut state_issue = None;
        let previous = match fs::read(&state_path) {
            Ok(bytes) => {
                match serde_json::from_slice::<Observation>(&bytes) {
                    Ok(p) if p.version == 1 && p.task_key == key => Some(p),
                    _ => {
                        state_issue = Some("incompatible_or_malformed_state");
                        None
                    }
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
            Err(_) => {
                state_issue = Some("state_read");
                None
            }
        };
        let mut category = "cold";
        let mut changed = vec![];
        if let Some(p) = &previous {
            category = "unknown";
            if coverage.is_empty()
                && p.coverage.is_empty()
                && slots.keys().eq(p.slots.keys())
                && slots.iter().all(|(k, s)| {
                    p.slots[k].fingerprint == s.fingerprint && p.slots[k].role == s.role
                })
            {
                let mut head = false;
                let mut body = false;
                for (k, s) in &slots {
                    let old = &p.slots[k];
                    if old.formula.parameters != s.formula.parameters {
                        category = "unknown";
                        changed.clear();
                        head = false;
                        body = false;
                        break;
                    }
                    if old.formula.body != s.formula.body {
                        head |= matches!(s.role.as_str(), "head" | "both");
                        body |= matches!(s.role.as_str(), "body" | "both");
                        changed.push(k.clone());
                    }
                }
                if slots
                    .iter()
                    .all(|(k, s)| p.slots[k].formula.parameters == s.formula.parameters)
                {
                    category = match (head, body) {
                        (false, false) => "unchanged",
                        (true, false) => "heads_only",
                        (false, true) => "bodies_only",
                        (true, true) => "both",
                    };
                }
            }
        }
        let shared_ms = start.elapsed().as_secs_f64() * 1000.0;
        let mut experiments = vec![];
        if let Some(p) = &previous
            && evaluate
        {
            if category == "unchanged" {
                experiments.push(timed("unchanged", || Ok(json!({"outcome":match p.safe {Some(true)=>"predict_pass",Some(false)=>"predict_fail",None=>"unavailable"}}))));
            }
            let candidate = p.result.as_ref();
            if category == "heads_only" {
                experiments.push(self.head_experiment("heads_all", task, candidate, p, false));
                experiments.push(self.head_experiment("heads_selective", task, candidate, p, true));
            }
            if matches!(category, "bodies_only" | "both") {
                let strengthening = || -> Result<Value, String> {
                    let formulas = changed
                        .iter()
                        .filter(|k| matches!(slots[*k].role.as_str(), "body" | "both"))
                        .map(|k| {
                            Formula {
                                parameters: slots[k].formula.parameters.clone(),
                                body: format!(
                                    "(=> {} {})",
                                    slots[k].formula.body, p.slots[k].formula.body
                                ),
                            }
                        })
                        .collect::<Vec<_>>();
                    let statuses = check_formulas("", &formulas, config::vc_reuse_budget())?;
                    Ok(
                        json!({"outcome":outcome(&statuses),"implication_queries":formulas.len(),"results":statuses}),
                    )
                };
                let mut strength = timed("body_strengthening", strengthening);
                let stronger = strength["outcome"] == "predict_pass";
                // Strengthening by itself predicts query PASS only after previous PASS
                // and with no changed concrete heads.
                strength["implications_valid"] = stronger.into();
                if !(category == "bodies_only" && p.safe == Some(true)) && stronger {
                    strength["outcome"] = "implications_valid".into();
                }
                let strength_ms = strength["total_ms"].as_f64().unwrap_or_default();
                experiments.push(strength);
                if stronger && p.safe.is_some() {
                    let mut heads = self.head_experiment(
                        "strengthened_bodies_heads_all",
                        task,
                        candidate,
                        p,
                        false,
                    );
                    heads["prerequisite_ms"] = strength_ms.into();
                    experiments.push(heads);
                    // Exact passing-clause matching is conservative: changed bodies
                    // won't match; they are checked instead of guessing alignment.
                    let mut selective = self.head_experiment(
                        "strengthened_bodies_heads_selective",
                        task,
                        candidate,
                        p,
                        true,
                    );
                    selective["prerequisite_ms"] = strength_ms.into();
                    experiments.push(selective);
                    if category == "both" && p.safe == Some(true) {
                        let mut weak = timed("body_strengthening_head_weakening", || {
                            let formulas = changed
                                .iter()
                                .filter(|k| matches!(slots[*k].role.as_str(), "head" | "both"))
                                .map(|k| {
                                    Formula {
                                        parameters: slots[k].formula.parameters.clone(),
                                        body: format!(
                                            "(=> {} {})",
                                            p.slots[k].formula.body, slots[k].formula.body
                                        ),
                                    }
                                })
                                .collect::<Vec<_>>();
                            let statuses =
                                check_formulas("", &formulas, config::vc_reuse_budget())?;
                            Ok(
                                json!({"outcome":outcome(&statuses),"implication_queries":formulas.len(),"results":statuses}),
                            )
                        });
                        weak["prerequisite_ms"] = strength_ms.into();
                        experiments.push(weak);
                    }
                }
            }
            experiments.push(timed("whole_vc", || {
                let c = candidate.ok_or("missing_candidate")?;
                let prepared = task.prepare_solution_clauses(c, |s| self.try_parse_kvar_solution(s))?;
                let formulas = prepared.clauses.iter().map(|c| c.formula.clone()).collect::<Vec<_>>();
                let statuses = check_formulas(&prepared.declarations, &formulas, config::vc_reuse_budget())?;
                Ok(json!({"outcome":outcome(&statuses),"clauses_checked":formulas.len(),"results":statuses}))
            }));
        }
        let record = json!({"schema_version":1,"crate":crate_name,"task_key":key,"task_hash":task.hash_with_default(),"previous_task_hash":previous.as_ref().map(|p|p.hash),"previous_safe":previous.as_ref().and_then(|p|p.safe),"change_category":category,"changed_slots":changed,"coverage":coverage,"state_issue":state_issue,"shared_preparation_ms":shared_ms,"assumptions":"signature-only edits; current marker coverage and role semantics","experiments":experiments});
        ExperimentRun { state_path, record, slots, coverage }
    }

    fn head_experiment(
        &mut self,
        name: &str,
        task: &fixpoint::Task,
        candidate: Option<&VerificationResult<TagIdx>>,
        previous: &Observation,
        selective: bool,
    ) -> Value {
        timed(name, || {
            let candidate = candidate.ok_or("missing_candidate")?;
            let prepared =
                task.prepare_solution_clauses(candidate, |s| self.try_parse_kvar_solution(s))?;
            let passing = if selective
                && previous
                    .prepared
                    .as_ref()
                    .is_some_and(|p| p.declarations == prepared.declarations)
            {
                previous
                    .prepared
                    .as_ref()
                    .unwrap()
                    .clauses
                    .iter()
                    .zip(&previous.clause_results)
                    .filter(|(_, s)| s.as_str() == "valid")
                    .map(|(c, _)| c.fingerprint.as_str())
                    .collect::<BTreeSet<_>>()
            } else {
                BTreeSet::new()
            };
            let mut skipped = 0;
            let formulas = prepared
                .clauses
                .iter()
                .filter(|c| c.concrete)
                .filter(|c| {
                    if passing.contains(c.fingerprint.as_str()) {
                        skipped += 1;
                        false
                    } else {
                        true
                    }
                })
                .map(|c| c.formula.clone())
                .collect::<Vec<_>>();
            let statuses =
                check_formulas(&prepared.declarations, &formulas, config::vc_reuse_budget())?;
            Ok(
                json!({"outcome":outcome(&statuses),"clauses_checked":formulas.len(),"clauses_skipped":skipped,"results":statuses}),
            )
        })
    }

    pub(super) fn finish_reuse_experiments(
        &mut self,
        mut run: ExperimentRun,
        task: &fixpoint::Task,
        result: Option<&VerificationResult<TagIdx>>,
        fixpoint_ms: Option<f64>,
        reference_path: &str,
    ) {
        let safe = result.and_then(|r| {
            match r.status {
                FixpointStatus::Safe(_) => Some(true),
                FixpointStatus::Unsafe(..) => Some(false),
                _ => None,
            }
        });
        let mut disagreements = vec![];
        let experiments = run.record["experiments"].as_array().unwrap();
        for e in experiments {
            if (e["outcome"] == "predict_pass" && safe == Some(false))
                || (e["outcome"] == "predict_fail" && safe == Some(true))
            {
                disagreements
                    .push(format!("{}:prediction_vs_fixpoint", e["name"].as_str().unwrap()));
            }
        }
        for (all, selective) in [
            ("heads_all", "heads_selective"),
            ("strengthened_bodies_heads_all", "strengthened_bodies_heads_selective"),
        ] {
            if experiments
                .iter()
                .any(|e| e["name"] == all && e["outcome"] == "candidate_rejected")
                && experiments
                    .iter()
                    .any(|e| e["name"] == selective && e["outcome"] == "predict_pass")
            {
                disagreements.push(format!("{selective}:selective_vs_all"));
            }
        }
        run.record["reference"] = json!({"path":reference_path,"safe":safe,"fixpoint_ms":fixpoint_ms,"cached_equivalent":reference_path=="exact_hit"});
        run.record["disagreements"] = json!(disagreements);
        let evidence_start = Instant::now();
        let prepared_result =
            result.map(|r| task.prepare_solution_clauses(r, |s| self.try_parse_kvar_solution(s)));
        let mut evidence_reason = prepared_result
            .as_ref()
            .and_then(|r| r.as_ref().err())
            .cloned();
        let prepared = prepared_result.and_then(Result::ok);
        let clause_results = match prepared.as_ref().map(|p| {
            check_formulas(
                &p.declarations,
                &p.clauses
                    .iter()
                    .map(|c| c.formula.clone())
                    .collect::<Vec<_>>(),
                config::vc_reuse_budget(),
            )
        }) {
            Some(Ok(statuses)) => statuses,
            Some(Err(reason)) => {
                evidence_reason = Some(reason);
                vec![]
            }
            None => vec![],
        };
        run.record["fresh_evidence_ms"] = (evidence_start.elapsed().as_secs_f64() * 1000.0).into();
        run.record["fresh_evidence_results"] = json!(clause_results);
        run.record["fresh_evidence_reason"] = json!(evidence_reason);
        run.record["budget_ms"] = json!(config::vc_reuse_budget().as_millis());
        let observation = Observation {
            version: 1,
            task_key: run.record["task_key"].as_str().unwrap().into(),
            hash: task.hash_with_default(),
            safe,
            slots: run.slots,
            coverage: run.coverage,
            result: result.cloned(),
            prepared,
            clause_results,
        };
        let write = || -> Result<(), Box<dyn std::error::Error>> {
            fs::create_dir_all(config::vc_reuse_state())?;
            let tmp = run
                .state_path
                .with_extension(format!("{}.tmp", std::process::id()));
            fs::write(&tmp, serde_json::to_vec(&observation)?)?;
            fs::rename(tmp, &run.state_path)?;
            fs::create_dir_all(config::log_dir())?;
            let path = config::log_dir().join(format!(
                "{}-vc-reuse-experiments.jsonl",
                self.genv.tcx().crate_name(rustc_hir::def_id::LOCAL_CRATE)
            ));
            let mut file = fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)?;
            serde_json::to_writer(&mut file, &run.record)?;
            writeln!(file)?;
            Ok(())
        };
        if let Err(e) = write() {
            eprintln!("VC reuse diagnostic output failed: {e}");
        }
    }
}
