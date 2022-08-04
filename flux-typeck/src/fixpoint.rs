use std::{fs, io::Write, iter};

use fixpoint::FixpointResult;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;

use flux_common::{
    config::CONFIG,
    index::{IndexGen, IndexVec},
};
use flux_fixpoint as fixpoint;
use flux_middle::{
    global_env,
    ty::{self, BoundVar, KVid},
};
use rustc_middle::ty::TyCtxt;

use crate::refine_tree::Scope;

newtype_index! {
    pub struct TagIdx {
        DEBUG_FORMAT = "TagIdx({})"
    }
}

#[derive(Default)]
pub struct KVarStore {
    kvars: IndexVec<KVid, Vec<fixpoint::Sort>>,
}

pub trait KVarGen {
    fn fresh<S>(&mut self, sorts: &[ty::Sort], scope: S) -> ty::Pred
    where
        S: IntoIterator<Item = (ty::Name, ty::Sort)>;

    fn chaining<'a>(&'a mut self, scope: &'a Scope) -> KVarGenScopeChain<'a, Self> {
        KVarGenScopeChain { kvar_gen: self, scope }
    }
}

pub struct KVarGenScopeChain<'a, G: ?Sized> {
    kvar_gen: &'a mut G,
    scope: &'a Scope,
}

type NameMap = FxHashMap<ty::Name, fixpoint::Name>;
type ConstMap = FxHashMap<DefId, ConstInfo>;

pub struct FixpointCtxt<T> {
    kvars: KVarStore,
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

impl<T> FixpointCtxt<T>
where
    T: std::hash::Hash + Eq + Copy,
{
    pub fn new(const_infos: &[global_env::ConstInfo], kvars: KVarStore) -> Self {
        let name_gen = IndexGen::new();
        let const_map = fixpoint_const_map(const_infos, &name_gen);
        Self {
            kvars,
            name_gen,
            name_map: FxHashMap::default(),
            const_map,
            tags: IndexVec::new(),
            tags_inv: FxHashMap::default(),
        }
    }

    pub fn with_name_map<R>(
        &mut self,
        name: ty::Name,
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
        fixpoint::Constraint::Guard(e1.eq(e2), Box::new(cstr))
    }

    pub fn check(
        self,
        tcx: TyCtxt,
        did: DefId,
        constraint: fixpoint::Constraint<TagIdx>,
        qualifiers: &[ty::Qualifier],
    ) -> Result<(), Vec<T>> {
        let kvars = self.kvars.into_fixpoint();

        let mut closed_constraint = constraint;
        for const_info in self.const_map.values() {
            closed_constraint = Self::assume_const_val(closed_constraint, const_info);
        }

        let qualifiers = qualifiers
            .iter()
            .map(|qual| qualifier_to_fixpoint(&self.const_map, qual))
            .collect();

        let constants = self
            .const_map
            .iter()
            .map(|(_, const_info)| (const_info.name, fixpoint::Sort::Int))
            .collect();

        let task = fixpoint::Task::new(constants, kvars, closed_constraint, qualifiers);
        if CONFIG.dump_constraint {
            dump_constraint(tcx, did, &task, ".smt2").unwrap();
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

    pub fn tag_idx(&mut self, tag: T) -> TagIdx {
        *self
            .tags_inv
            .entry(tag)
            .or_insert_with(|| self.tags.push(tag))
    }

    pub fn expr_to_fixpoint(&self, expr: &ty::Expr) -> fixpoint::Expr {
        expr_to_fixpoint(expr, &self.name_map, &self.const_map)
    }

    pub fn pred_to_fixpoint(
        &mut self,
        bindings: &mut Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>,
        pred: &ty::Pred,
    ) -> fixpoint::Pred {
        match pred {
            ty::Pred::Expr(expr) => {
                fixpoint::Pred::Expr(expr_to_fixpoint(expr, &self.name_map, &self.const_map))
            }
            ty::Pred::Kvars(kvars) => {
                let kvars = kvars
                    .iter()
                    .map(|kvar| self.kvar_to_fixpoint(bindings, kvar))
                    .collect();
                fixpoint::Pred::And(kvars)
            }
            ty::Pred::Hole => panic!("unexpected hole"),
        }
    }

    fn kvar_to_fixpoint(
        &mut self,
        bindings: &mut Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>,
        ty::KVar(kvid, args): &ty::KVar,
    ) -> fixpoint::Pred {
        let args = iter::zip(args, &self.kvars[*kvid]).map(|(arg, sort)| {
            match arg.kind() {
                ty::ExprKind::FreeVar(name) => {
                    *self
                        .name_map
                        .get(name)
                        .unwrap_or_else(|| panic!("no entry found for key: `{name:?}`"))
                }
                ty::ExprKind::BoundVar(_) => panic!("unexpected free bound variable"),
                _ => {
                    let fresh = self.fresh_name();
                    let pred = fixpoint::Expr::BinaryOp(
                        fixpoint::BinOp::Eq,
                        Box::new(fixpoint::Expr::Var(fresh)),
                        Box::new(expr_to_fixpoint(arg, &self.name_map, &self.const_map)),
                    );
                    bindings.push((fresh, sort.clone(), pred));
                    fresh
                }
            }
        });
        fixpoint::Pred::KVar(*kvid, args.collect())
    }
}

fn fixpoint_const_map(
    const_infos: &[global_env::ConstInfo],
    name_gen: &IndexGen<fixpoint::Name>,
) -> FxHashMap<DefId, ConstInfo> {
    const_infos
        .iter()
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

    pub fn fresh<S>(&mut self, sorts: &[ty::Sort], scope: S) -> ty::Pred
    where
        S: IntoIterator<Item = (ty::Name, ty::Sort)>,
    {
        let scope = scope.into_iter();

        let mut args = scope
            .filter(|(_, sort)| !sort.is_loc())
            .map(|(name, sort)| (ty::Expr::fvar(name), sort))
            .collect_vec();

        let mut kvars = vec![];
        for (idx, sort) in sorts.iter().enumerate() {
            args.push((ty::Expr::bvar(BoundVar::innermost(idx)), sort.clone()));

            let kvid = self.kvars.push(
                args.iter()
                    .rev()
                    .map(|(_, s)| sort_to_fixpoint(s))
                    .collect(),
            );
            kvars
                .push(ty::KVar::new(kvid, args.iter().rev().map(|(e, _)| e.clone()).collect_vec()));
        }
        ty::Pred::kvars(kvars)
    }

    pub fn into_fixpoint(self) -> Vec<fixpoint::KVar> {
        self.kvars
            .into_iter_enumerated()
            .map(|(kvid, sorts)| fixpoint::KVar(kvid, sorts))
            .collect()
    }
}

impl KVarGen for KVarStore {
    fn fresh<S>(&mut self, sorts: &[ty::Sort], scope: S) -> ty::Pred
    where
        S: IntoIterator<Item = (ty::Name, ty::Sort)>,
    {
        KVarStore::fresh(self, sorts, scope)
    }
}

impl<G> KVarGen for KVarGenScopeChain<'_, G>
where
    G: KVarGen,
{
    fn fresh<S>(&mut self, sorts: &[ty::Sort], scope: S) -> ty::Pred
    where
        S: IntoIterator<Item = (ty::Name, ty::Sort)>,
    {
        self.kvar_gen.fresh(sorts, self.scope.iter().chain(scope))
    }
}

impl std::ops::Index<KVid> for KVarStore {
    type Output = Vec<fixpoint::Sort>;

    fn index(&self, index: KVid) -> &Self::Output {
        &self.kvars[index]
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

pub fn sort_to_fixpoint(sort: &ty::Sort) -> fixpoint::Sort {
    match sort {
        ty::Sort::Int | ty::Sort::Loc => fixpoint::Sort::Int,
        ty::Sort::Bool => fixpoint::Sort::Bool,
        ty::Sort::Tuple(sorts) => {
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

fn qualifier_to_fixpoint(const_map: &ConstMap, qualifier: &ty::Qualifier) -> fixpoint::Qualifier {
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
    fixpoint::Qualifier { name, args, expr }
}

fn expr_to_fixpoint(expr: &ty::Expr, name_map: &NameMap, const_map: &ConstMap) -> fixpoint::Expr {
    match expr.kind() {
        ty::ExprKind::FreeVar(name) => {
            let name = name_map
                .get(name)
                .unwrap_or_else(|| panic!("no entry found for key: `{name:?}`"));
            fixpoint::Expr::Var(*name)
        }
        ty::ExprKind::Constant(c) => fixpoint::Expr::Constant(*c),
        ty::ExprKind::BinaryOp(op, e1, e2) => {
            fixpoint::Expr::BinaryOp(
                *op,
                Box::new(expr_to_fixpoint(e1, name_map, const_map)),
                Box::new(expr_to_fixpoint(e2, name_map, const_map)),
            )
        }
        ty::ExprKind::UnaryOp(op, e) => {
            fixpoint::Expr::UnaryOp(*op, Box::new(expr_to_fixpoint(e, name_map, const_map)))
        }
        ty::ExprKind::TupleProj(e, field) => {
            itertools::repeat_n(fixpoint::Proj::Snd, *field as usize)
                .chain([fixpoint::Proj::Fst])
                .fold(expr_to_fixpoint(e, name_map, const_map), |e, proj| {
                    fixpoint::Expr::Proj(Box::new(e), proj)
                })
        }
        ty::ExprKind::Tuple(exprs) => tuple_to_fixpoint(exprs, name_map, const_map),
        ty::ExprKind::Local(_) | ty::ExprKind::BoundVar(_) | ty::ExprKind::PathProj(..) => {
            panic!("unexpected expr: `{expr:?}`")
        }
        ty::ExprKind::ConstDefId(did) => fixpoint::Expr::Var(const_map[did].name),
    }
}

fn tuple_to_fixpoint(
    exprs: &[ty::Expr],
    name_map: &NameMap,
    const_map: &ConstMap,
) -> fixpoint::Expr {
    match exprs {
        [] => fixpoint::Expr::Unit,
        [e, exprs @ ..] => {
            fixpoint::Expr::Pair(
                Box::new(expr_to_fixpoint(e, name_map, const_map)),
                Box::new(tuple_to_fixpoint(exprs, name_map, const_map)),
            )
        }
    }
}
