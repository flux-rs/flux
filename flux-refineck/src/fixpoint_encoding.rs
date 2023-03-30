///! Encoding of the refinement tree into a fixpoint constraint.
use std::iter;

use fixpoint::FixpointResult;
use flux_common::{
    bug,
    cache::QueryCache,
    dbg,
    index::{IndexGen, IndexVec},
    span_bug,
};
use flux_config as config;
use flux_fixpoint as fixpoint;
use flux_middle::{
    fhir::FuncKind,
    global_env::GlobalEnv,
    queries::QueryResult,
    rty::{self, Constant},
};
use itertools::{self, Itertools};
use rustc_data_structures::fx::FxIndexMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_span::Span;

newtype_index! {
    #[debug_format = "TagIdx({})"]
    pub struct TagIdx {}
}

#[derive(Default)]
pub struct KVarStore {
    kvars: IndexVec<rty::KVid, KVarDecl>,
}

#[derive(Clone)]
struct KVarDecl {
    self_args: usize,
    sorts: Vec<rty::Sort>,
    encoding: KVarEncoding,
}

/// How an [`rty::KVar`] is encoded in the fixpoint constraint
#[derive(Clone, Copy)]
pub enum KVarEncoding {
    /// Generate a single kvar appending the self arguments and the scope, i.e.,
    /// a kvar `$k(a0, ...)[b0, ...]` becomes `$k(a0, ..., b0, ...)` in the fixpoint constraint.
    Single,
    /// Generate a conjunction of kvars, one per argument in [rty::KVar::args].
    /// Concretely, a kvar `$k(a0, a1, ..., an)[b0, ...]` becomes
    /// `$k0(a0, a1, ..., an, b0, ...) ∧ $k1(a1, ..., an, b0, ...) ∧ ... ∧ $kn(an, b0, ...)`
    Conj,
}

type NameMap = FxHashMap<rty::Name, fixpoint::Name>;
type KVidMap = FxHashMap<rty::KVid, Vec<fixpoint::KVid>>;
type ConstMap = FxIndexMap<Key, ConstInfo>;

#[derive(Eq, Hash, PartialEq)]
enum Key {
    Uif(rustc_span::Symbol),
    Const(DefId),
}

pub struct FixpointCtxt<'genv, 'tcx, T> {
    comments: Vec<String>,
    genv: &'genv GlobalEnv<'genv, 'tcx>,
    kvars: KVarStore,
    fixpoint_kvars: IndexVec<fixpoint::KVid, FixpointKVar>,
    kvid_map: KVidMap,
    name_gen: IndexGen<fixpoint::Name>,
    name_map: NameMap,
    const_map: ConstMap,
    tags: IndexVec<TagIdx, T>,
    tags_inv: FxHashMap<T, TagIdx>,
    /// [`DefId`] of the item being checked. This could be a function/method or an adt when checking
    /// invariants.
    def_id: DefId,
}

struct FixpointKVar {
    sorts: Vec<fixpoint::Sort>,
    orig: rty::KVid,
}

struct ExprCtxt<'a> {
    name_map: &'a NameMap,
    const_map: &'a ConstMap,
    /// Used to report bugs
    dbg_span: Span,
}

#[derive(Debug)]
struct ConstInfo {
    name: fixpoint::ConstName,
    sym: rustc_span::Symbol,
    sort: fixpoint::Sort,
    val: Option<Constant>,
}

impl<'genv, 'tcx, Tag> FixpointCtxt<'genv, 'tcx, Tag>
where
    Tag: std::hash::Hash + Eq + Copy,
{
    pub fn new(genv: &'genv GlobalEnv<'genv, 'tcx>, def_id: DefId, kvars: KVarStore) -> Self {
        let name_gen = IndexGen::new();
        let const_map = fixpoint_const_map(genv);
        Self {
            comments: vec![],
            kvars,
            genv,
            name_gen,
            fixpoint_kvars: IndexVec::new(),
            kvid_map: KVidMap::default(),
            name_map: NameMap::default(),
            const_map,
            tags: IndexVec::new(),
            tags_inv: FxHashMap::default(),
            def_id,
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
        const_name: fixpoint::ConstName,
        const_val: Constant,
    ) -> fixpoint::Constraint<TagIdx> {
        let e1 = fixpoint::Expr::from(const_name);
        let e2 = fixpoint::Expr::Constant(const_val);
        let pred = fixpoint::Pred::Expr(e1.eq(e2));
        fixpoint::Constraint::Guard(pred, Box::new(cstr))
    }

    pub fn check(
        self,
        cache: &mut QueryCache,
        constraint: fixpoint::Constraint<TagIdx>,
    ) -> QueryResult<Vec<Tag>> {
        if !constraint.is_concrete() {
            // skip checking trivial constraints
            return Ok(vec![]);
        }
        let span = self.def_span();

        let kvars = self
            .fixpoint_kvars
            .into_iter_enumerated()
            .map(|(kvid, kvar)| {
                fixpoint::KVar::new(kvid, kvar.sorts, format!("orig: {:?}", kvar.orig))
            })
            .collect_vec();

        let mut closed_constraint = constraint;
        for const_info in self.const_map.values() {
            if let Some(val) = const_info.val {
                closed_constraint = Self::assume_const_val(closed_constraint, const_info.name, val);
            }
        }

        let qualifiers = self
            .genv
            .qualifiers(self.def_id)?
            .map(|qual| qualifier_to_fixpoint(span, &self.const_map, qual))
            .collect();

        let constants = self
            .const_map
            .into_values()
            .map(|const_info| {
                fixpoint::ConstInfo {
                    name: const_info.name,
                    orig: const_info.sym,
                    sort: const_info.sort,
                }
            })
            .collect();

        let sorts = self
            .genv
            .map()
            .sort_decls()
            .values()
            .map(|sort_decl| sort_decl.name.to_string())
            .collect_vec();

        let task = fixpoint::Task::new(
            self.comments,
            constants,
            kvars,
            closed_constraint,
            qualifiers,
            sorts,
        );
        if config::dump_constraint() {
            dbg::dump_item_info(self.genv.tcx, self.def_id, "smt2", &task).unwrap();
        }

        let task_key = self.genv.tcx.def_path_str(self.def_id);

        match task.check_with_cache(task_key, cache) {
            Ok(FixpointResult::Safe(_)) => Ok(vec![]),
            Ok(FixpointResult::Unsafe(_, errors)) => {
                Ok(errors
                    .into_iter()
                    .map(|err| self.tags[err.tag])
                    .unique()
                    .collect_vec())
            }
            Ok(FixpointResult::Crash(err)) => span_bug!(span, "fixpoint crash: {err:?}"),
            Err(err) => span_bug!(span, "failed to run fixpoint: {err:?}"),
        }
    }

    pub fn tag_idx(&mut self, tag: Tag) -> TagIdx
    where
        Tag: std::fmt::Debug,
    {
        *self.tags_inv.entry(tag).or_insert_with(|| {
            let idx = self.tags.push(tag);
            self.comments.push(format!("Tag {idx}: {tag:?}"));
            idx
        })
    }

    pub fn pred_to_fixpoint(
        &mut self,
        pred: &rty::Expr,
    ) -> (Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>, fixpoint::Pred) {
        let mut bindings = vec![];
        let mut preds = vec![];
        self.pred_to_fixpoint_internal(pred, &mut bindings, &mut preds);
        (bindings, fixpoint::Pred::And(preds))
    }

    fn pred_to_fixpoint_internal(
        &mut self,
        expr: &rty::Expr,
        bindings: &mut Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>,
        preds: &mut Vec<fixpoint::Pred>,
    ) {
        match expr.kind() {
            rty::ExprKind::BinaryOp(rty::BinOp::And, e1, e2) => {
                self.pred_to_fixpoint_internal(e1, bindings, preds);
                self.pred_to_fixpoint_internal(e2, bindings, preds);
            }
            rty::ExprKind::KVar(kvar) => {
                preds.push(self.kvar_to_fixpoint(kvar, bindings));
            }
            _ => {
                preds.push(fixpoint::Pred::Expr(self.as_expr_cx().expr_to_fixpoint(expr)));
            }
        }
    }

    fn kvar_to_fixpoint(
        &mut self,
        kvar: &rty::KVar,
        bindings: &mut Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>,
    ) -> fixpoint::Pred {
        self.populate_kvid_map(kvar.kvid);

        let decl = self.kvars.get(kvar.kvid);

        let all_args = iter::zip(&kvar.args, &decl.sorts)
            .map(|(arg, sort)| self.imm(arg, sort, bindings))
            .collect_vec();

        let kvids = &self.kvid_map[&kvar.kvid];

        if all_args.is_empty() {
            let fresh = self.fresh_name();
            bindings.push((
                fresh,
                fixpoint::Sort::Unit,
                fixpoint::Expr::eq(fixpoint::Expr::Var(fresh), fixpoint::Expr::Unit),
            ));
            return fixpoint::Pred::KVar(kvids[0], vec![fresh]);
        }

        let kvars = kvids
            .iter()
            .enumerate()
            .map(|(i, kvid)| {
                let args = all_args.iter().skip(kvids.len() - i - 1).copied().collect();
                fixpoint::Pred::KVar(*kvid, args)
            })
            .collect_vec();

        fixpoint::Pred::And(kvars)
    }

    fn populate_kvid_map(&mut self, kvid: rty::KVid) {
        self.kvid_map.entry(kvid).or_insert_with(|| {
            let decl = self.kvars.get(kvid);

            let all_args = decl.sorts.iter().map(sort_to_fixpoint).collect_vec();

            if all_args.is_empty() {
                let sorts = vec![fixpoint::Sort::Unit];
                let kvid = self.fixpoint_kvars.push(FixpointKVar::new(sorts, kvid));
                return vec![kvid];
            }

            match decl.encoding {
                KVarEncoding::Single => {
                    let kvid = self.fixpoint_kvars.push(FixpointKVar::new(all_args, kvid));
                    vec![kvid]
                }
                KVarEncoding::Conj => {
                    let n = usize::max(decl.self_args, 1);
                    (0..n)
                        .map(|i| {
                            let sorts = all_args.iter().skip(n - i - 1).cloned().collect();
                            self.fixpoint_kvars.push(FixpointKVar::new(sorts, kvid))
                        })
                        .collect_vec()
                }
            }
        });
    }

    fn imm(
        &self,
        arg: &rty::Expr,
        sort: &rty::Sort,
        bindings: &mut Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>,
    ) -> fixpoint::Name {
        match arg.kind() {
            rty::ExprKind::Var(rty::Var::Free(name)) => {
                *self.name_map.get(name).unwrap_or_else(|| {
                    span_bug!(self.def_span(), "no entry found for key: `{name:?}`")
                })
            }
            rty::ExprKind::Var(_) => {
                span_bug!(self.def_span(), "unexpected variable")
            }
            _ => {
                let fresh = self.fresh_name();
                let pred = fixpoint::Expr::eq(
                    fixpoint::Expr::Var(fresh),
                    self.as_expr_cx().expr_to_fixpoint(arg),
                );
                bindings.push((fresh, sort_to_fixpoint(sort), pred));
                fresh
            }
        }
    }

    fn as_expr_cx(&self) -> ExprCtxt<'_> {
        ExprCtxt::new(&self.name_map, &self.const_map, self.def_span())
    }

    fn def_span(&self) -> Span {
        self.genv.tcx.def_span(self.def_id)
    }
}

impl FixpointKVar {
    fn new(sorts: Vec<fixpoint::Sort>, orig: rty::KVid) -> Self {
        Self { sorts, orig }
    }
}

fn fixpoint_const_map(genv: &GlobalEnv) -> ConstMap {
    let const_name_gen = IndexGen::new();
    let consts = genv
        .map()
        .consts()
        .sorted_by(|a, b| Ord::cmp(&a.sym, &b.sym))
        .map(|const_info| {
            let name = const_name_gen.fresh();
            let cinfo = ConstInfo {
                name,
                sym: const_info.sym,
                sort: fixpoint::Sort::Int,
                val: Some(const_info.val),
            };
            (Key::Const(const_info.def_id), cinfo)
        });
    let uifs = genv
        .func_decls()
        .sorted_by(|a, b| Ord::cmp(&a.name, &b.name))
        .filter_map(|decl| {
            match decl.kind {
                FuncKind::Uif => {
                    let name = const_name_gen.fresh();
                    let sort = func_sort_to_fixpoint(&decl.sort);
                    let cinfo = ConstInfo {
                        name,
                        sym: decl.name,
                        sort: fixpoint::Sort::Func(sort),
                        val: None,
                    };
                    Some((Key::Uif(cinfo.sym), cinfo))
                }
                _ => None,
            }
        });
    itertools::chain(consts, uifs).collect()
}

impl KVarStore {
    pub fn new() -> Self {
        Self { kvars: IndexVec::new() }
    }

    fn get(&self, kvid: rty::KVid) -> &KVarDecl {
        &self.kvars[kvid]
    }

    pub fn fresh<A>(&mut self, self_args: usize, args: A, encoding: KVarEncoding) -> rty::Expr
    where
        A: IntoIterator<Item = (rty::Var, rty::Sort)>,
    {
        let mut sorts = vec![];
        let mut exprs = vec![];

        let mut flattened_self_args = 0;
        for (i, (var, sort)) in args.into_iter().enumerate() {
            let is_self_arg = i < self_args;
            let var = var.to_expr();
            sort.walk(|sort, proj| {
                if !matches!(sort, rty::Sort::Loc | rty::Sort::Func(..)) {
                    flattened_self_args += is_self_arg as usize;
                    sorts.push(sort.clone());
                    exprs.push(rty::Expr::tuple_projs(&var, proj));
                }
            });
        }

        let kvid = self
            .kvars
            .push(KVarDecl { self_args: flattened_self_args, sorts, encoding });

        let kvar = rty::KVar::new(kvid, flattened_self_args, exprs);
        rty::Expr::kvar(kvar)
    }

    pub fn fresh_bound<S>(
        &mut self,
        bound: &[rty::Sort],
        scope: S,
        encoding: KVarEncoding,
    ) -> rty::Expr
    where
        S: IntoIterator<Item = (rty::Name, rty::Sort)>,
    {
        if bound.is_empty() {
            return self.fresh(0, [], encoding);
        }
        let args = itertools::chain(
            bound.iter().rev().enumerate().map(|(level, sort)| {
                (rty::Var::LateBound(rty::DebruijnIndex::new(level as u32)), sort.clone())
            }),
            scope
                .into_iter()
                .map(|(name, sort)| (rty::Var::Free(name), sort)),
        );
        self.fresh(1, args, encoding)
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
        rty::Sort::Real => fixpoint::Sort::Real,
        rty::Sort::Bool => fixpoint::Sort::Bool,
        rty::Sort::BitVec(w) => fixpoint::Sort::BitVec(*w),
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
        // There's no way to declare sorts in the horn syntax in fixpoint so we encode
        // user declared opaque sorts and type variable sorts as integers. Well-formedness
        // should ensure values of these sorts are properly used.
        rty::Sort::User(_) | rty::Sort::Param(_) => fixpoint::Sort::Int,
        rty::Sort::Func(sort) => fixpoint::Sort::Func(func_sort_to_fixpoint(sort)),
        rty::Sort::Loc => bug!("unexpected sort {sort:?}"),
    }
}

fn func_sort_to_fixpoint(fsort: &rty::FuncSort) -> fixpoint::FuncSort {
    fixpoint::FuncSort::new(
        fsort.input().as_tuple().iter().map(sort_to_fixpoint),
        sort_to_fixpoint(fsort.output()),
    )
}

impl<'a> ExprCtxt<'a> {
    fn new(name_map: &'a NameMap, const_map: &'a ConstMap, dbg_span: Span) -> Self {
        Self { name_map, const_map, dbg_span }
    }

    fn expr_to_fixpoint(&self, expr: &rty::Expr) -> fixpoint::Expr {
        match expr.kind() {
            rty::ExprKind::Var(rty::Var::Free(name)) => {
                let name = self.name_map.get(name).unwrap_or_else(|| {
                    span_bug!(self.dbg_span, "no entry found in name_map for name: `{name:?}`")
                });
                fixpoint::Expr::Var(*name)
            }
            rty::ExprKind::Constant(c) => fixpoint::Expr::Constant(*c),
            rty::ExprKind::BinaryOp(op, e1, e2) => {
                fixpoint::Expr::BinaryOp(
                    *op,
                    Box::new([self.expr_to_fixpoint(e1), self.expr_to_fixpoint(e2)]),
                )
            }
            rty::ExprKind::UnaryOp(op, e) => {
                fixpoint::Expr::UnaryOp(*op, Box::new(self.expr_to_fixpoint(e)))
            }
            rty::ExprKind::TupleProj(e, field) => {
                itertools::repeat_n(fixpoint::Proj::Snd, *field as usize)
                    .chain([fixpoint::Proj::Fst])
                    .fold(self.expr_to_fixpoint(e), |e, proj| {
                        fixpoint::Expr::Proj(Box::new(e), proj)
                    })
            }
            rty::ExprKind::Tuple(exprs) => self.tuple_to_fixpoint(exprs),
            rty::ExprKind::ConstDefId(did) => {
                let const_info = self.const_map.get(&Key::Const(*did)).unwrap_or_else(|| {
                    span_bug!(self.dbg_span, "no entry found in const_map for def_id: `{did:?}`")
                });
                fixpoint::Expr::ConstVar(const_info.name)
            }
            rty::ExprKind::App(func, arg) => {
                let func = self.func_to_fixpoint(func);
                let arg = self.exprs_to_fixpoint(arg.as_tuple());
                fixpoint::Expr::App(func, arg)
            }
            rty::ExprKind::IfThenElse(p, e1, e2) => {
                fixpoint::Expr::IfThenElse(Box::new([
                    self.expr_to_fixpoint(p),
                    self.expr_to_fixpoint(e1),
                    self.expr_to_fixpoint(e2),
                ]))
            }
            rty::ExprKind::Var(_)
            | rty::ExprKind::Hole
            | rty::ExprKind::KVar(_)
            | rty::ExprKind::Local(_)
            | rty::ExprKind::Abs(_)
            | rty::ExprKind::Func(_)
            | rty::ExprKind::PathProj(..) => {
                span_bug!(self.dbg_span, "unexpected expr: `{expr:?}`")
            }
        }
    }

    fn exprs_to_fixpoint<'b>(
        &self,
        exprs: impl IntoIterator<Item = &'b rty::Expr>,
    ) -> Vec<fixpoint::Expr> {
        exprs
            .into_iter()
            .map(|e| self.expr_to_fixpoint(e))
            .collect()
    }

    fn tuple_to_fixpoint(&self, exprs: &[rty::Expr]) -> fixpoint::Expr {
        match exprs {
            [] => fixpoint::Expr::Unit,
            [e, exprs @ ..] => {
                fixpoint::Expr::Pair(Box::new([
                    self.expr_to_fixpoint(e),
                    self.tuple_to_fixpoint(exprs),
                ]))
            }
        }
    }

    fn func_to_fixpoint(&self, func: &rty::Expr) -> fixpoint::Func {
        match func.kind() {
            rty::ExprKind::Var(rty::Var::Free(name)) => {
                let name = self.name_map.get(name).unwrap_or_else(|| {
                    span_bug!(self.dbg_span, "no name found for key: `{name:?}`")
                });
                fixpoint::Func::Var(*name)
            }
            rty::ExprKind::Func(name) => {
                if let Some(cinfo) = self.const_map.get(&Key::Uif(*name)) {
                    fixpoint::Func::Uif(cinfo.name)
                } else {
                    fixpoint::Func::Itf(*name)
                }
            }
            _ => {
                span_bug!(self.dbg_span, "unexpected expr `{func:?}` in function position")
            }
        }
    }
}

fn qualifier_to_fixpoint(
    dbg_span: Span,
    const_map: &ConstMap,
    qualifier: &rty::Qualifier,
) -> fixpoint::Qualifier {
    let (args, body) = qualifier.with_fresh_fvars();
    let name_gen = IndexGen::skipping(const_map.len());
    let mut name_map = NameMap::default();
    let args = args
        .into_iter()
        .map(|(name, sort)| {
            let fresh = name_gen.fresh();
            name_map.insert(name, fresh);
            (fresh, sort_to_fixpoint(&sort))
        })
        .collect_vec();
    let name = qualifier.name.clone();
    let cx = ExprCtxt::new(&name_map, const_map, dbg_span);
    let body = cx.expr_to_fixpoint(&body);
    let global = qualifier.global;
    fixpoint::Qualifier { name, args, body, global }
}
