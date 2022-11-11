use std::{fs, io::Write, iter};

use fixpoint::FixpointResult;
use flux_common::{
    config::CONFIG,
    index::{IndexGen, IndexVec},
};
use flux_fixpoint as fixpoint;
use flux_middle::{
    fhir,
    global_env::GlobalEnv,
    rty::{self, Binders, BoundVar},
};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_middle::ty::TyCtxt;

use crate::refine_tree::Scope;

newtype_index! {
    pub struct TagIdx {
        DEBUG_FORMAT = "TagIdx({})"
    }
}

#[derive(Default)]
pub struct KVarStore {
    kvars: IndexVec<rty::KVid, KVarSorts>,
}

#[derive(Clone)]
struct KVarSorts {
    args: Vec<rty::Sort>,
    scope: Vec<rty::Sort>,
}

pub trait KVarGen {
    fn fresh<S>(&mut self, sorts: &[rty::Sort], scope: S) -> Binders<rty::Pred>
    where
        S: IntoIterator<Item = (rty::Name, rty::Sort)>;

    fn chaining<'a>(&'a mut self, scope: &'a Scope) -> KVarGenScopeChain<'a, Self> {
        KVarGenScopeChain { kvar_gen: self, scope }
    }
}

pub struct KVarGenScopeChain<'a, G: ?Sized> {
    kvar_gen: &'a mut G,
    scope: &'a Scope,
}

type NameMap = FxHashMap<rty::Name, fixpoint::Name>;
type KVidMap = FxHashMap<rty::KVid, Vec<fixpoint::KVid>>;
type ConstMap = FxHashMap<DefId, ConstInfo>;

pub struct FixpointCtxt<'genv, 'tcx, T> {
    genv: &'genv GlobalEnv<'genv, 'tcx>,
    kvars: KVarStore,
    fixpoint_kvars: IndexVec<fixpoint::KVid, Vec<fixpoint::Sort>>,
    kvid_map: KVidMap,
    name_gen: IndexGen<fixpoint::Name>,
    name_map: NameMap,
    const_map: ConstMap,
    tags: IndexVec<TagIdx, T>,
    tags_inv: FxHashMap<T, TagIdx>,
}

struct ConstInfo {
    name: fixpoint::Name,
    val: i128,
}

impl<'genv, 'tcx, Tag> FixpointCtxt<'genv, 'tcx, Tag>
where
    Tag: std::hash::Hash + Eq + Copy,
{
    pub fn new(genv: &'genv GlobalEnv<'genv, 'tcx>, kvars: KVarStore) -> Self {
        let name_gen = IndexGen::new();
        let const_map = fixpoint_const_map(genv, &name_gen);
        Self {
            kvars,
            genv,
            name_gen,
            fixpoint_kvars: IndexVec::new(),
            kvid_map: KVidMap::default(),
            name_map: NameMap::default(),
            const_map,
            tags: IndexVec::new(),
            tags_inv: FxHashMap::default(),
        }
    }

    pub fn with_name_map<R>(
        &mut self,
        name: rty::Name,
        to: fixpoint::Name,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.name_map.insert(name, to);
        let r = f(self);
        self.name_map.remove(&name);
        r
    }

    pub fn fresh_name(&self) -> fixpoint::Name {
        self.name_gen.fresh()
    }

    fn assume_const_val(
        cstr: fixpoint::Constraint<TagIdx>,
        const_info: &ConstInfo,
    ) -> fixpoint::Constraint<TagIdx> {
        let name = const_info.name;
        let e1 = fixpoint::Expr::from(name);
        let e2 = fixpoint::Expr::from(const_info.val);
        let pred = fixpoint::Pred::Expr(e1.eq(e2));
        fixpoint::Constraint::Guard(pred, Box::new(cstr))
    }

    pub fn check(
        self,
        did: DefId,
        constraint: fixpoint::Constraint<TagIdx>,
    ) -> Result<(), Vec<Tag>> {
        let kvars = self
            .fixpoint_kvars
            .into_iter_enumerated()
            .map(|(kvid, sorts)| fixpoint::KVar(kvid, sorts))
            .collect_vec();

        let mut closed_constraint = constraint;
        for const_info in self.const_map.values() {
            closed_constraint = Self::assume_const_val(closed_constraint, const_info);
        }

        let qualifiers = self
            .genv
            .qualifiers
            .iter()
            .map(|qual| qualifier_to_fixpoint(&self.const_map, qual))
            .collect();

        let constants = self
            .const_map
            .values()
            .map(|const_info| (const_info.name, fixpoint::Sort::Int))
            .collect();

        let uifs = self
            .genv
            .map()
            .uifs()
            .map(uif_def_to_fixpoint)
            .collect_vec();

        let task = fixpoint::Task::new(constants, kvars, closed_constraint, qualifiers, uifs);
        if CONFIG.dump_constraint {
            dump_constraint(self.genv.tcx, did, &task, ".smt2").unwrap();
        }

        match task.check() {
            Ok(FixpointResult::Safe(_)) => Ok(()),
            Ok(FixpointResult::Unsafe(_, errors)) => {
                Err(errors
                    .into_iter()
                    .map(|err| self.tags[err.tag])
                    .unique()
                    .collect_vec())
            }
            Ok(FixpointResult::Crash(err)) => panic!("fixpoint crash: {err:?}"),
            Err(err) => panic!("failed to run fixpoint: {err:?}"),
        }
    }

    pub fn tag_idx(&mut self, tag: Tag) -> TagIdx {
        *self
            .tags_inv
            .entry(tag)
            .or_insert_with(|| self.tags.push(tag))
    }

    pub fn pred_to_fixpoint(
        &mut self,
        pred: &rty::Pred,
    ) -> (Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>, fixpoint::Pred) {
        let mut bindings = vec![];
        let pred = self.pred_to_fixpoint_internal(pred, &mut bindings);
        (bindings, pred)
    }

    fn pred_to_fixpoint_internal(
        &mut self,
        pred: &rty::Pred,
        bindings: &mut Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>,
    ) -> fixpoint::Pred {
        match pred {
            rty::Pred::And(preds) => {
                fixpoint::Pred::And(
                    preds
                        .iter()
                        .map(|p| self.pred_to_fixpoint_internal(p, bindings))
                        .collect(),
                )
            }
            rty::Pred::Expr(expr) => {
                let expr = expr_to_fixpoint(expr, &self.name_map, &self.const_map);
                fixpoint::Pred::Expr(expr)
            }
            rty::Pred::Kvar(kvar) => self.kvar_to_fixpoint(kvar, bindings),
            rty::Pred::App(rty::Var::Free(name), args) => {
                let name = self
                    .name_map
                    .get(name)
                    .unwrap_or_else(|| panic!("no entry found for key: `{name:?}`"));
                let func = fixpoint::Func::Var(*name);
                let args = exprs_to_fixpoint(args, &self.name_map, &self.const_map);
                fixpoint::Pred::Expr(fixpoint::Expr::App(func, args))
            }
            rty::Pred::App(rty::Var::Bound(_), _) => {
                panic!("unexpected bound var in pred application")
            }
            rty::Pred::Hole => panic!("unexpected hole"),
        }
    }

    fn kvar_to_fixpoint(
        &mut self,
        kvar: &rty::KVar,
        bindings: &mut Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>,
    ) -> fixpoint::Pred {
        self.populate_kvid_map(kvar.kvid);

        let sorts = self.kvars.get(kvar.kvid);

        let mut scope = iter::zip(&kvar.scope, &sorts.scope)
            .map(|(arg, sort)| self.imm(arg, sort, bindings))
            .collect_vec();

        let kvids = &self.kvid_map[&kvar.kvid];
        let mut kvars = vec![];
        for (kvid, arg, sort) in itertools::izip!(kvids, &kvar.args, &sorts.args) {
            let arg = self.imm(arg, sort, bindings);

            let mut args = vec![arg];
            args.extend(scope.iter().copied());

            kvars.push(fixpoint::Pred::KVar(*kvid, args));

            scope.push(arg);
        }

        fixpoint::Pred::And(kvars)
    }

    fn imm(
        &self,
        arg: &rty::Expr,
        sort: &rty::Sort,
        bindings: &mut Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>,
    ) -> fixpoint::Name {
        match arg.kind() {
            rty::ExprKind::FreeVar(name) => {
                *self
                    .name_map
                    .get(name)
                    .unwrap_or_else(|| panic!("no entry found for key: `{name:?}`"))
            }
            rty::ExprKind::BoundVar(_) => panic!("unexpected free bound variable"),
            _ => {
                let fresh = self.fresh_name();
                let pred = fixpoint::Expr::BinaryOp(
                    fixpoint::BinOp::Eq,
                    Box::new([
                        fixpoint::Expr::Var(fresh),
                        expr_to_fixpoint(arg, &self.name_map, &self.const_map),
                    ]),
                );
                bindings.push((fresh, sort_to_fixpoint(sort), pred));
                fresh
            }
        }
    }

    fn populate_kvid_map(&mut self, kvid: rty::KVid) {
        self.kvid_map.entry(kvid).or_insert_with(|| {
            let sorts = self.kvars.get(kvid);

            let mut scope = sorts.scope.iter().map(sort_to_fixpoint).collect_vec();

            let mut kvids = vec![];
            for sort in &sorts.args {
                let sort = sort_to_fixpoint(sort);

                let kvid = self.fixpoint_kvars.push({
                    let mut sorts = vec![sort.clone()];
                    sorts.extend(scope.iter().cloned());
                    sorts
                });
                kvids.push(kvid);

                scope.push(sort);
            }

            kvids
        });
    }
}

fn fixpoint_const_map(
    genv: &GlobalEnv,
    name_gen: &IndexGen<fixpoint::Name>,
) -> FxHashMap<DefId, ConstInfo> {
    genv.map()
        .consts()
        .map(|const_info| {
            let name = name_gen.fresh();
            let cinfo = ConstInfo { name, val: const_info.val };
            (const_info.def_id, cinfo)
        })
        .collect()
}

impl KVarStore {
    pub fn new() -> Self {
        Self { kvars: IndexVec::new() }
    }

    fn get(&self, kvid: rty::KVid) -> &KVarSorts {
        &self.kvars[kvid]
    }

    pub fn fresh<S>(&mut self, sorts: &[rty::Sort], scope: S) -> Binders<rty::Pred>
    where
        S: IntoIterator<Item = (rty::Name, rty::Sort)>,
    {
        let mut scope_sorts = vec![];
        let mut scope_exprs = vec![];
        for (name, sort) in scope {
            if !sort.is_loc() {
                scope_sorts.push(sort);
                scope_exprs.push(rty::Expr::fvar(name));
            }
        }

        let args = (0..sorts.len())
            .map(|idx| rty::Expr::bvar(BoundVar::innermost(idx)))
            .collect_vec();

        let kvid = self
            .kvars
            .push(KVarSorts { args: sorts.to_vec(), scope: scope_sorts.clone() });

        Binders::new(rty::Pred::Kvar(rty::KVar::new(kvid, args, scope_exprs.clone())), sorts)
    }
}

impl KVarGen for KVarStore {
    fn fresh<S>(&mut self, sorts: &[rty::Sort], scope: S) -> Binders<rty::Pred>
    where
        S: IntoIterator<Item = (rty::Name, rty::Sort)>,
    {
        KVarStore::fresh(self, sorts, scope)
    }
}

impl<G> KVarGen for KVarGenScopeChain<'_, G>
where
    G: KVarGen,
{
    fn fresh<S>(&mut self, sorts: &[rty::Sort], scope: S) -> Binders<rty::Pred>
    where
        S: IntoIterator<Item = (rty::Name, rty::Sort)>,
    {
        self.kvar_gen.fresh(sorts, self.scope.iter().chain(scope))
    }
}

impl std::fmt::Display for TagIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_u32())
    }
}

impl std::str::FromStr for TagIdx {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from_u32(s.parse()?))
    }
}

pub fn sort_to_fixpoint(sort: &rty::Sort) -> fixpoint::Sort {
    match sort {
        rty::Sort::Int => fixpoint::Sort::Int,
        rty::Sort::Bool => fixpoint::Sort::Bool,
        rty::Sort::Tuple(sorts) => {
            match &sorts[..] {
                [] => fixpoint::Sort::Unit,
                [_] => unreachable!("1-tuple"),
                [sorts @ .., s1, s2] => {
                    let s1 = Box::new(sort_to_fixpoint(s1));
                    let s2 = Box::new(sort_to_fixpoint(s2));
                    sorts
                        .iter()
                        .map(sort_to_fixpoint)
                        .map(Box::new)
                        .fold(fixpoint::Sort::Pair(s1, s2), |s1, s2| {
                            fixpoint::Sort::Pair(Box::new(s1), s2)
                        })
                }
            }
        }
        rty::Sort::Func(sort) => fixpoint::Sort::Func(func_sort_to_fixpoint(sort)),
        rty::Sort::Loc => unreachable!("unexpected sort {sort:?}"),
    }
}

fn func_sort_to_fixpoint(sort: &rty::FuncSort) -> fixpoint::FuncSort {
    fixpoint::FuncSort {
        inputs_and_output: sort
            .inputs_and_output
            .iter()
            .map(sort_to_fixpoint)
            .collect(),
    }
}

/// TODO(nilehmann) we should abstract over the dumping files logic
fn dump_constraint<C: std::fmt::Debug>(
    tcx: TyCtxt,
    def_id: DefId,
    c: &C,
    suffix: &str,
) -> Result<(), std::io::Error> {
    let dir = CONFIG.log_dir.join("horn");
    fs::create_dir_all(&dir)?;
    let mut file = fs::File::create(dir.join(format!("{}{}", tcx.def_path_str(def_id), suffix)))?;
    write!(file, "{:?}", c)
}

fn uif_def_to_fixpoint(uif_def: &fhir::UifDef) -> fixpoint::UifDef {
    let sort = func_sort_to_fixpoint(&uif_def.sort);
    fixpoint::UifDef::new(uif_def.name.to_string(), sort)
}

fn qualifier_to_fixpoint(const_map: &ConstMap, qualifier: &rty::Qualifier) -> fixpoint::Qualifier {
    let name_gen = IndexGen::skipping(const_map.len());
    let mut name_map = NameMap::default();
    let name = qualifier.name.clone();
    let args = qualifier
        .args
        .iter()
        .map(|(name, sort)| {
            let fresh = name_gen.fresh();
            name_map.insert(*name, fresh);
            (fresh, sort_to_fixpoint(sort))
        })
        .collect();

    let expr = expr_to_fixpoint(&qualifier.expr, &name_map, const_map);
    fixpoint::Qualifier { expr, args, name }
}

fn expr_to_fixpoint(expr: &rty::Expr, name_map: &NameMap, const_map: &ConstMap) -> fixpoint::Expr {
    match expr.kind() {
        rty::ExprKind::FreeVar(name) => {
            let name = name_map
                .get(name)
                .unwrap_or_else(|| panic!("no entry found for key: `{name:?}`"));
            fixpoint::Expr::Var(*name)
        }
        rty::ExprKind::Constant(c) => fixpoint::Expr::Constant(*c),
        rty::ExprKind::BinaryOp(op, e1, e2) => {
            fixpoint::Expr::BinaryOp(
                *op,
                Box::new([
                    expr_to_fixpoint(e1, name_map, const_map),
                    expr_to_fixpoint(e2, name_map, const_map),
                ]),
            )
        }
        rty::ExprKind::UnaryOp(op, e) => {
            fixpoint::Expr::UnaryOp(*op, Box::new(expr_to_fixpoint(e, name_map, const_map)))
        }
        rty::ExprKind::TupleProj(e, field) => {
            itertools::repeat_n(fixpoint::Proj::Snd, *field as usize)
                .chain([fixpoint::Proj::Fst])
                .fold(expr_to_fixpoint(e, name_map, const_map), |e, proj| {
                    fixpoint::Expr::Proj(Box::new(e), proj)
                })
        }
        rty::ExprKind::Tuple(exprs) => tuple_to_fixpoint(exprs, name_map, const_map),
        rty::ExprKind::Local(_) | rty::ExprKind::BoundVar(_) | rty::ExprKind::PathProj(..) => {
            panic!("unexpected expr: `{expr:?}`")
        }
        rty::ExprKind::ConstDefId(did) => fixpoint::Expr::Var(const_map[did].name),
        rty::ExprKind::App(func, args) => {
            let args = exprs_to_fixpoint(args, name_map, const_map);
            let uif = fixpoint::Func::Uif(func.to_string());
            fixpoint::Expr::App(uif, args)
        }
        rty::ExprKind::IfThenElse(p, e1, e2) => {
            fixpoint::Expr::IfThenElse(Box::new([
                expr_to_fixpoint(p, name_map, const_map),
                expr_to_fixpoint(e1, name_map, const_map),
                expr_to_fixpoint(e2, name_map, const_map),
            ]))
        }
    }
}

fn exprs_to_fixpoint<'a>(
    exprs: impl IntoIterator<Item = &'a rty::Expr>,
    name_map: &NameMap,
    const_map: &ConstMap,
) -> Vec<fixpoint::Expr> {
    exprs
        .into_iter()
        .map(|e| expr_to_fixpoint(e, name_map, const_map))
        .collect()
}

fn tuple_to_fixpoint(
    exprs: &[rty::Expr],
    name_map: &NameMap,
    const_map: &ConstMap,
) -> fixpoint::Expr {
    match exprs {
        [] => fixpoint::Expr::Unit,
        [e, exprs @ ..] => {
            fixpoint::Expr::Pair(Box::new([
                expr_to_fixpoint(e, name_map, const_map),
                tuple_to_fixpoint(exprs, name_map, const_map),
            ]))
        }
    }
}
