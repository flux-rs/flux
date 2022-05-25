use std::{fs, io::Write, iter};

use fixpoint::FixpointResult;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;

use liquid_rust_common::{
    config::CONFIG,
    index::{IndexGen, IndexVec},
};
use liquid_rust_fixpoint as fixpoint;
use liquid_rust_middle::ty::{self, KVid};
use rustc_middle::ty::TyCtxt;

newtype_index! {
    pub struct TagIdx {
        DEBUG_FORMAT = "TagIdx({})"
    }
}

#[derive(Default)]
pub struct KVarStore {
    kvars: IndexVec<KVid, Vec<fixpoint::Sort>>,
}

type NameMap = FxHashMap<ty::Name, fixpoint::Name>;

pub struct FixpointCtxt<T> {
    kvars: KVarStore,
    name_gen: IndexGen<fixpoint::Name>,
    name_map: NameMap,
    tags: IndexVec<TagIdx, T>,
    tags_inv: FxHashMap<T, TagIdx>,
}

impl<T> FixpointCtxt<T>
where
    T: std::hash::Hash + Eq + Copy,
{
    pub fn new(kvars: KVarStore) -> Self {
        Self {
            kvars,
            name_gen: IndexGen::new(),
            name_map: FxHashMap::default(),
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

    pub fn check(
        self,
        tcx: TyCtxt,
        did: DefId,
        constraint: fixpoint::Constraint<TagIdx>,
        qualifiers: &[ty::Qualifier],
    ) -> Result<(), Vec<T>> {
        let kvars = self.kvars.into_fixpoint();

        let qualifiers = qualifiers.iter().map(qualifier_to_fixpoint).collect();

        let task = fixpoint::Task::new(kvars, constraint, qualifiers);
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
        expr_to_fixpoint(expr, &self.name_map)
    }

    pub fn pred_to_fixpoint(
        &mut self,
        bindings: &mut Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>,
        pred: &ty::Pred,
    ) -> fixpoint::Pred {
        match pred {
            ty::Pred::Expr(expr) => fixpoint::Pred::Expr(expr_to_fixpoint(expr, &self.name_map)),
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
                        Box::new(expr_to_fixpoint(arg, &self.name_map)),
                    );
                    bindings.push((fresh, sort.clone(), pred));
                    fresh
                }
            }
        });
        fixpoint::Pred::KVar(*kvid, args.collect())
    }
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
            .filter(|(_, s)| !matches!(s.kind(), ty::SortKind::Loc))
            .map(|(name, sort)| (ty::Expr::fvar(name), sort))
            .collect_vec();

        let mut kvars = vec![];
        for (i, sort) in sorts.iter().enumerate() {
            args.push((ty::Expr::bvar(i as u32), sort.clone()));

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

fn sort_to_fixpoint(sort: &ty::Sort) -> fixpoint::Sort {
    match sort.kind() {
        ty::SortKind::Int | ty::SortKind::Loc => fixpoint::Sort::Int,
        ty::SortKind::Bool => fixpoint::Sort::Bool,
        ty::SortKind::Tuple(sorts) => {
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

fn qualifier_to_fixpoint(qualifier: &ty::Qualifier) -> fixpoint::Qualifier {
    let name_gen = IndexGen::new();
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

    let expr = expr_to_fixpoint(&qualifier.expr, &name_map);
    fixpoint::Qualifier { name, args, expr }
}

fn expr_to_fixpoint(expr: &ty::Expr, name_map: &NameMap) -> fixpoint::Expr {
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
                Box::new(expr_to_fixpoint(e1, name_map)),
                Box::new(expr_to_fixpoint(e2, name_map)),
            )
        }
        ty::ExprKind::UnaryOp(op, e) => {
            fixpoint::Expr::UnaryOp(*op, Box::new(expr_to_fixpoint(e, name_map)))
        }
        ty::ExprKind::BoundVar(_) => panic!("unexpected free bound variable"),
        ty::ExprKind::Proj(e, field) => {
            itertools::repeat_n(fixpoint::Proj::Snd, *field as usize)
                .chain([fixpoint::Proj::Fst])
                .fold(expr_to_fixpoint(e, name_map), |e, proj| {
                    fixpoint::Expr::Proj(Box::new(e), proj)
                })
        }
        ty::ExprKind::Tuple(exprs) => tuple_to_fixpoint(exprs, name_map),
        ty::ExprKind::Path(_) => panic!("unexpected path"),
    }
}

fn tuple_to_fixpoint(exprs: &[ty::Expr], name_map: &NameMap) -> fixpoint::Expr {
    match exprs {
        [] => fixpoint::Expr::Unit,
        [e, exprs @ ..] => {
            fixpoint::Expr::Pair(
                Box::new(expr_to_fixpoint(e, name_map)),
                Box::new(tuple_to_fixpoint(exprs, name_map)),
            )
        }
    }
}
