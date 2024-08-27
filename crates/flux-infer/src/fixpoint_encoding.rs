//! Encoding of the refinement tree into a fixpoint constraint.

use std::{hash::Hash, iter};

use flux_common::{
    bug,
    cache::QueryCache,
    dbg,
    index::{IndexGen, IndexVec},
    iter::IterExt,
    span_bug,
};
use flux_config as config;
use flux_errors::Errors;
use flux_fixpoint::FixpointResult;
use flux_middle::{
    const_eval,
    fhir::{self, SpecFuncKind},
    global_env::GlobalEnv,
    intern::List,
    pretty,
    queries::QueryResult,
    rty::{self, Constant, ESpan, Lambda},
};
use itertools::Itertools;
use rustc_data_structures::{
    fx::FxIndexMap,
    unord::{UnordMap, UnordSet},
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::newtype_index;
use rustc_span::{Span, Symbol};
use rustc_type_ir::{BoundVar, DebruijnIndex};

pub mod fixpoint {
    use std::fmt;

    use flux_middle::rty::EarlyReftParam;
    use rustc_index::newtype_index;
    use rustc_middle::ty::ParamConst;
    use rustc_span::Symbol;

    newtype_index! {
        pub struct KVid {}
    }

    impl fmt::Display for KVid {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "k{}", self.as_u32())
        }
    }

    newtype_index! {
        pub struct LocalVar {}
    }

    newtype_index! {
        pub struct GlobalVar {}
    }

    #[derive(Hash, Copy, Clone)]
    pub enum Var {
        Underscore,
        Global(GlobalVar),
        Local(LocalVar),
        TupleCtor {
            arity: usize,
        },
        TupleProj {
            arity: usize,
            field: u32,
        },
        UIFRel(BinRel),
        /// Interpreted theory function. This can be an arbitrary string, thus we are assuming the
        /// name is different than the display implementation for the other variants.
        Itf(Symbol),
        Param(EarlyReftParam),
        ConstGeneric(ParamConst),
    }

    impl From<GlobalVar> for Var {
        fn from(v: GlobalVar) -> Self {
            Self::Global(v)
        }
    }

    impl From<LocalVar> for Var {
        fn from(v: LocalVar) -> Self {
            Self::Local(v)
        }
    }

    impl fmt::Display for Var {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Var::Global(v) => write!(f, "c{}", v.as_u32()),
                Var::Local(v) => write!(f, "a{}", v.as_u32()),
                Var::TupleCtor { arity } => write!(f, "mktuple{arity}"),
                Var::TupleProj { arity, field } => write!(f, "tuple{arity}${field}"),
                Var::Itf(name) => write!(f, "{name}"),
                Var::UIFRel(BinRel::Gt) => write!(f, "gt"),
                Var::UIFRel(BinRel::Ge) => write!(f, "ge"),
                Var::UIFRel(BinRel::Lt) => write!(f, "lt"),
                Var::UIFRel(BinRel::Le) => write!(f, "le"),
                // these are actually not necessary because equality is interpreted for all sorts
                Var::UIFRel(BinRel::Eq) => write!(f, "eq"),
                Var::UIFRel(BinRel::Ne) => write!(f, "ne"),
                Var::Underscore => write!(f, "_$"), // To avoid clashing with `_` used for `app (_ bv_op n)` for parametric SMT ops
                Var::ConstGeneric(param) => {
                    write!(f, "constgen{}#{}", param.name, param.index)
                }
                Var::Param(param) => {
                    write!(f, "reftgen{}#{}", param.name, param.index)
                }
            }
        }
    }

    #[derive(Clone, Hash)]
    pub enum DataSort {
        Tuple(usize),
    }

    impl fmt::Display for DataSort {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                DataSort::Tuple(arity) => {
                    write!(f, "Tuple{arity}")
                }
            }
        }
    }

    flux_fixpoint::declare_types! {
        type Sort = DataSort;
        type KVar = KVid;
        type Var = Var;
        type Tag = super::TagIdx;
    }
    pub use fixpoint_generated::*;
}

newtype_index! {
    #[debug_format = "TagIdx({})"]
    pub struct TagIdx {}
}

/// Keep track of all the data sorts that we need to define in fixpoint to encode the constraint.
/// Currently, we encode all aggregate sorts as tuples.
#[derive(Default)]
struct SortEncodingCtxt {
    /// Set of all the tuple arities that need to be defined
    tuples: UnordSet<usize>,
}

impl SortEncodingCtxt {
    fn sort_to_fixpoint(&mut self, sort: &rty::Sort) -> fixpoint::Sort {
        match sort {
            rty::Sort::Int => fixpoint::Sort::Int,
            rty::Sort::Real => fixpoint::Sort::Real,
            rty::Sort::Bool => fixpoint::Sort::Bool,
            rty::Sort::Str => fixpoint::Sort::Str,
            rty::Sort::BitVec(size) => fixpoint::Sort::BitVec(Box::new(bv_size_to_fixpoint(*size))),
            // There's no way to declare user defined sorts in the fixpoint horn syntax so we encode
            // user declared opaque sorts and type variable sorts as integers. Well-formedness should
            // ensure values of these sorts are properly used.
            rty::Sort::App(rty::SortCtor::User { .. }, _) | rty::Sort::Param(_) => {
                fixpoint::Sort::Int
            }
            rty::Sort::App(rty::SortCtor::Set, args) => {
                let args = args.iter().map(|s| self.sort_to_fixpoint(s)).collect_vec();
                fixpoint::Sort::App(fixpoint::SortCtor::Set, args)
            }
            rty::Sort::App(rty::SortCtor::Map, args) => {
                let args = args.iter().map(|s| self.sort_to_fixpoint(s)).collect_vec();
                fixpoint::Sort::App(fixpoint::SortCtor::Map, args)
            }
            rty::Sort::App(rty::SortCtor::Adt(sort_def), args) => {
                self.declare_tuple(sort_def.fields());
                let ctor = fixpoint::SortCtor::Data(fixpoint::DataSort::Tuple(sort_def.fields()));
                let args = sort_def
                    .field_sorts(args)
                    .iter()
                    .map(|s| self.sort_to_fixpoint(s))
                    .collect_vec();
                fixpoint::Sort::App(ctor, args)
            }
            rty::Sort::Tuple(sorts) => {
                self.declare_tuple(sorts.len());
                let ctor = fixpoint::SortCtor::Data(fixpoint::DataSort::Tuple(sorts.len()));
                let args = sorts.iter().map(|s| self.sort_to_fixpoint(s)).collect();
                fixpoint::Sort::App(ctor, args)
            }
            rty::Sort::Func(sort) => self.func_sort_to_fixpoint(sort),
            rty::Sort::Var(k) => fixpoint::Sort::Var(k.index),
            rty::Sort::Err | rty::Sort::Infer(_) | rty::Sort::Loc => {
                bug!("unexpected sort {sort:?}")
            }
        }
    }

    fn func_sort_to_fixpoint(&mut self, fsort: &rty::PolyFuncSort) -> fixpoint::Sort {
        let params = fsort.params().len();
        let fsort = fsort.skip_binders();
        fixpoint::Sort::mk_func(
            params,
            fsort
                .inputs()
                .iter()
                .map(|s| self.sort_to_fixpoint(s))
                .collect_vec(),
            self.sort_to_fixpoint(fsort.output()),
        )
    }

    fn declare_tuple(&mut self, arity: usize) {
        self.tuples.insert(arity);
    }

    fn into_data_decls(self) -> Vec<fixpoint::DataDecl> {
        self.tuples
            .into_items()
            .into_sorted_stable_ord()
            .into_iter()
            .map(|arity| {
                fixpoint::DataDecl {
                    name: fixpoint::DataSort::Tuple(arity),
                    vars: arity,
                    ctors: vec![fixpoint::DataCtor {
                        name: fixpoint::Var::TupleCtor { arity },
                        fields: (0..(arity as u32))
                            .map(|field| {
                                fixpoint::DataField {
                                    name: fixpoint::Var::TupleProj { arity, field },
                                    sort: fixpoint::Sort::Var(field as usize),
                                }
                            })
                            .collect(),
                    }],
                }
            })
            .collect()
    }
}

fn bv_size_to_fixpoint(size: rty::BvSize) -> fixpoint::Sort {
    match size {
        rty::BvSize::Fixed(size) => fixpoint::Sort::BvSize(size),
        rty::BvSize::Param(_var) => {
            // I think we could encode the size as a sort variable, but this would require some care
            // because smtlib doesn't really support parametric sizes. Fixpoint is probably already
            // too liberal about this and it'd be easy to make it crash.
            // fixpoint::Sort::Var(var.index)
            bug!("unexpected parametric bit-vector size")
        }
        rty::BvSize::Infer(_) => bug!("unexpected infer variable for bit-vector size"),
    }
}

type ConstMap<'tcx> = FxIndexMap<Key<'tcx>, ConstInfo>;

#[derive(Eq, Hash, PartialEq)]
enum Key<'tcx> {
    Uif(Symbol),
    Const(DefId),
    Alias(rustc_middle::ty::TraitRef<'tcx>),
    Lambda(Lambda),
}

pub struct FixpointCtxt<'genv, 'tcx, T: Eq + Hash> {
    comments: Vec<String>,
    genv: GlobalEnv<'genv, 'tcx>,
    kvars: KVarGen,
    scx: SortEncodingCtxt,
    kcx: KVarEncodingCtxt,
    ecx: ExprEncodingCtxt<'genv, 'tcx>,
    tags: IndexVec<TagIdx, T>,
    tags_inv: UnordMap<T, TagIdx>,
    /// [`DefId`] of the item being checked. This can be a function/method or an adt when checking
    /// invariants.
    def_id: LocalDefId,
}

impl<'genv, 'tcx, Tag> FixpointCtxt<'genv, 'tcx, Tag>
where
    Tag: std::hash::Hash + Eq + Copy,
{
    pub fn new(genv: GlobalEnv<'genv, 'tcx>, def_id: LocalDefId, kvars: KVarGen) -> Self {
        let def_span = genv.tcx().def_span(def_id);
        Self {
            comments: vec![],
            kvars,
            scx: SortEncodingCtxt::default(),
            genv,
            ecx: ExprEncodingCtxt::new(genv, def_span),
            kcx: Default::default(),
            tags: IndexVec::new(),
            tags_inv: Default::default(),
            def_id,
        }
    }

    pub(crate) fn with_name_map<R>(
        &mut self,
        name: rty::Name,
        f: impl FnOnce(&mut Self, fixpoint::LocalVar) -> R,
    ) -> R {
        let fresh = self.ecx.local_var_env.insert_fvar_map(name);
        let r = f(self, fresh);
        self.ecx.local_var_env.remove_fvar_map(name);
        r
    }

    fn assume_const_val(
        cstr: fixpoint::Constraint,
        var: fixpoint::GlobalVar,
        const_val: Constant,
    ) -> fixpoint::Constraint {
        let e1 = fixpoint::Expr::Var(fixpoint::Var::Global(var));
        let e2 = fixpoint::Expr::Constant(const_val);
        let pred = fixpoint::Pred::Expr(e1.eq(e2));
        fixpoint::Constraint::ForAll(
            fixpoint::Bind { name: fixpoint::Var::Underscore, sort: fixpoint::Sort::Int, pred },
            Box::new(cstr),
        )
    }

    fn fixpoint_const_info(const_info: ConstInfo) -> fixpoint::ConstInfo {
        fixpoint::ConstInfo {
            name: fixpoint::Var::Global(const_info.name),
            orig: Some(const_info.orig),
            sort: const_info.sort,
        }
    }

    pub fn check(
        mut self,
        cache: &mut QueryCache,
        constraint: fixpoint::Constraint,
        scrape_quals: bool,
    ) -> QueryResult<Vec<Tag>> {
        if !constraint.is_concrete() {
            // skip checking trivial constraints
            self.ecx.errors.into_result()?;
            return Ok(vec![]);
        }
        let def_span = self.def_span();

        let kvars = self
            .kcx
            .kvars
            .into_iter_enumerated()
            .map(|(kvid, kvar)| {
                fixpoint::KVar::new(kvid, kvar.sorts, format!("orig: {:?}", kvar.orig))
            })
            .collect_vec();

        let mut constraint = constraint;
        for const_info in self.ecx.const_map.values() {
            if let Some(val) = const_info.val {
                constraint = Self::assume_const_val(constraint, const_info.name, val);
            }
        }

        let qualifiers = self
            .genv
            .qualifiers_for(self.def_id)?
            .map(|qual| self.ecx.qualifier_to_fixpoint(qual, &mut self.scx))
            .try_collect()?;

        let mut constants = self
            .ecx
            .const_map
            .into_values()
            .map(Self::fixpoint_const_info)
            .collect_vec();

        for rel in fixpoint::BinRel::INEQUALITIES {
            // ∀a. a -> a -> bool
            let sort = fixpoint::Sort::mk_func(
                1,
                [fixpoint::Sort::Var(0), fixpoint::Sort::Var(0)],
                fixpoint::Sort::Bool,
            );
            constants.push(fixpoint::ConstInfo {
                name: fixpoint::Var::UIFRel(rel),
                sort,
                orig: None,
            });
        }

        // Check if the encoding produced any errors
        self.ecx.errors.into_result()?;

        let task = fixpoint::Task {
            comments: self.comments,
            constants,
            kvars,
            constraint,
            qualifiers,
            scrape_quals,
            data_decls: self.scx.into_data_decls(),
        };
        if config::dump_constraint() {
            dbg::dump_item_info(self.genv.tcx(), self.def_id, "smt2", &task).unwrap();
        }

        let task_key = self.genv.tcx().def_path_str(self.def_id);

        match task.check_with_cache(task_key, cache) {
            Ok(FixpointResult::Safe(_)) => Ok(vec![]),
            Ok(FixpointResult::Unsafe(_, errors)) => {
                Ok(errors
                    .into_iter()
                    .map(|err| self.tags[err.tag])
                    .unique()
                    .collect_vec())
            }
            Ok(FixpointResult::Crash(err)) => span_bug!(def_span, "fixpoint crash: {err:?}"),
            Err(err) => span_bug!(def_span, "failed to run fixpoint: {err:?}"),
        }
    }

    fn tag_idx(&mut self, tag: Tag) -> TagIdx
    where
        Tag: std::fmt::Debug,
    {
        *self.tags_inv.entry(tag).or_insert_with(|| {
            let idx = self.tags.push(tag);
            self.comments.push(format!("Tag {idx}: {tag:?}"));
            idx
        })
    }

    pub(crate) fn sort_to_fixpoint(&mut self, sort: &rty::Sort) -> fixpoint::Sort {
        self.scx.sort_to_fixpoint(sort)
    }

    pub(crate) fn var_to_fixpoint(&self, var: &rty::Var) -> fixpoint::Var {
        self.ecx.var_to_fixpoint(var)
    }

    /// Encodes an expression in head position as a [`fixpoint::Constraint`] "peeling out"
    /// implications and foralls.
    ///
    /// [`fixpoint::Constraint`]: flux_fixpoint::Constraint
    pub(crate) fn head_to_fixpoint(
        &mut self,
        expr: &rty::Expr,
        mk_tag: impl Fn(Option<ESpan>) -> Tag + Copy,
    ) -> QueryResult<fixpoint::Constraint>
    where
        Tag: std::fmt::Debug,
    {
        match expr.kind() {
            rty::ExprKind::BinaryOp(rty::BinOp::And, ..) => {
                // avoid creating nested conjunctions
                let cstrs = expr
                    .flatten_conjs()
                    .into_iter()
                    .map(|e| self.head_to_fixpoint(e, mk_tag))
                    .try_collect()?;
                Ok(fixpoint::Constraint::Conj(cstrs))
            }
            rty::ExprKind::BinaryOp(rty::BinOp::Imp, e1, e2) => {
                let (bindings, assumption) = self.assumption_to_fixpoint(e1)?;
                let cstr = self.head_to_fixpoint(e2, mk_tag)?;
                Ok(fixpoint::Constraint::foralls(bindings, mk_implies(assumption, cstr)))
            }
            rty::ExprKind::KVar(kvar) => {
                let mut bindings = vec![];
                let pred = self.kvar_to_fixpoint(kvar, &mut bindings)?;
                Ok(fixpoint::Constraint::foralls(bindings, fixpoint::Constraint::Pred(pred, None)))
            }
            rty::ExprKind::ForAll(pred) => {
                self.ecx
                    .local_var_env
                    .push_layer_with_fresh_names(pred.vars().len());
                let cstr = self.head_to_fixpoint(pred.as_ref().skip_binder(), mk_tag)?;
                let vars = self.ecx.local_var_env.pop_layer();

                let bindings = iter::zip(vars, &pred.vars().to_sort_list())
                    .map(|(var, sort)| {
                        fixpoint::Bind {
                            name: var.into(),
                            sort: self.scx.sort_to_fixpoint(sort),
                            pred: fixpoint::Pred::TRUE,
                        }
                    })
                    .collect_vec();

                Ok(fixpoint::Constraint::foralls(bindings, cstr))
            }
            _ => {
                let tag_idx = self.tag_idx(mk_tag(expr.span()));
                let pred = fixpoint::Pred::Expr(self.ecx.expr_to_fixpoint(expr, &mut self.scx)?);
                Ok(fixpoint::Constraint::Pred(pred, Some(tag_idx)))
            }
        }
    }

    /// Encodes an expression in assumptive position as a [`fixpoint::Pred`]. Returns the encoded
    /// predicate and a list of bindings produced by ANF-fing kvars.
    ///
    /// [`fixpoint::Pred`]: flux_fixpoint::Pred
    pub(crate) fn assumption_to_fixpoint(
        &mut self,
        pred: &rty::Expr,
    ) -> QueryResult<(Vec<fixpoint::Bind>, fixpoint::Pred)> {
        let mut bindings = vec![];
        let mut preds = vec![];
        self.assumption_to_fixpoint_aux(pred, &mut bindings, &mut preds)?;
        Ok((bindings, fixpoint::Pred::And(preds)))
    }

    /// Auxiliary function to avoid creating nested conjunctions
    fn assumption_to_fixpoint_aux(
        &mut self,
        expr: &rty::Expr,
        bindings: &mut Vec<fixpoint::Bind>,
        preds: &mut Vec<fixpoint::Pred>,
    ) -> QueryResult {
        match expr.kind() {
            rty::ExprKind::BinaryOp(rty::BinOp::And, e1, e2) => {
                self.assumption_to_fixpoint_aux(e1, bindings, preds)?;
                self.assumption_to_fixpoint_aux(e2, bindings, preds)?;
            }
            rty::ExprKind::KVar(kvar) => {
                preds.push(self.kvar_to_fixpoint(kvar, bindings)?);
            }
            rty::ExprKind::ForAll(_) => {
                // If a forall appears in assumptive position replace it with true. This is sound
                // because we are weakining the context, i.e., anything true without the assumption
                // should remaing true after adding it. Note that this relies on the predicate
                // appearing negatively. This is guaranteed by the surface syntax because foralls
                // can only appear at the top-level in a requires clause.
                preds.push(fixpoint::Pred::TRUE);
            }
            _ => {
                preds.push(fixpoint::Pred::Expr(self.ecx.expr_to_fixpoint(expr, &mut self.scx)?));
            }
        }
        Ok(())
    }

    fn kvar_to_fixpoint(
        &mut self,
        kvar: &rty::KVar,
        bindings: &mut Vec<fixpoint::Bind>,
    ) -> QueryResult<fixpoint::Pred> {
        let decl = self.kvars.get(kvar.kvid);
        let kvids = self.kcx.encode(kvar.kvid, decl, &mut self.scx);

        let all_args = iter::zip(&kvar.args, &decl.sorts)
            .map(|(arg, sort)| -> QueryResult<_> {
                self.ecx.imm(arg, sort, &mut self.scx, bindings)
            })
            .try_collect_vec()?;

        // Fixpoint doesn't support kvars without arguments, which we do generate sometimes. To get
        // around it, we encode `$k()` as ($k 0), or more precisley `(forall ((x int) (= x 0)) ... ($k x)`
        // after ANF-ing.
        if all_args.is_empty() {
            let fresh = self.ecx.local_var_env.fresh_name();
            let var = fixpoint::Var::Local(fresh);
            bindings.push(fixpoint::Bind {
                name: fresh.into(),
                sort: fixpoint::Sort::Int,
                pred: fixpoint::Pred::Expr(fixpoint::Expr::eq(
                    fixpoint::Expr::Var(var),
                    fixpoint::Expr::ZERO,
                )),
            });
            return Ok(fixpoint::Pred::KVar(kvids[0], vec![var]));
        }

        let kvars = kvids
            .iter()
            .enumerate()
            .map(|(i, kvid)| {
                let args = all_args.iter().skip(kvids.len() - i - 1).copied().collect();
                fixpoint::Pred::KVar(*kvid, args)
            })
            .collect_vec();

        Ok(fixpoint::Pred::And(kvars))
    }

    fn def_span(&self) -> Span {
        self.genv.tcx().def_span(self.def_id)
    }
}

struct FixpointKVar {
    sorts: Vec<fixpoint::Sort>,
    orig: rty::KVid,
}

/// During encoding into fixpoint we generate multiple fxpoint kvars per kvar in flux. A
/// [`KVarEncodingCtxt`] is used to keep track of the state needed for this.
#[derive(Default)]
struct KVarEncodingCtxt {
    /// List of all kvars that need to be defined in fixpoint
    kvars: IndexVec<fixpoint::KVid, FixpointKVar>,
    /// A mapping from [`rty::KVid`] to the list of [`fixpoint::KVid`]s encoding the kvar.
    map: UnordMap<rty::KVid, Vec<fixpoint::KVid>>,
}

impl KVarEncodingCtxt {
    fn encode(
        &mut self,
        kvid: rty::KVid,
        decl: &KVarDecl,
        scx: &mut SortEncodingCtxt,
    ) -> &[fixpoint::KVid] {
        self.map.entry(kvid).or_insert_with(|| {
            let all_args = decl
                .sorts
                .iter()
                .map(|s| scx.sort_to_fixpoint(s))
                .collect_vec();

            // See comment in `kvar_to_fixpoint`
            if all_args.is_empty() {
                let sorts = vec![fixpoint::Sort::Int];
                let kvid = self.kvars.push(FixpointKVar::new(sorts, kvid));
                return vec![kvid];
            }

            match decl.encoding {
                KVarEncoding::Single => {
                    let kvid = self.kvars.push(FixpointKVar::new(all_args, kvid));
                    vec![kvid]
                }
                KVarEncoding::Conj => {
                    let n = usize::max(decl.self_args, 1);
                    (0..n)
                        .map(|i| {
                            let sorts = all_args.iter().skip(n - i - 1).cloned().collect();
                            self.kvars.push(FixpointKVar::new(sorts, kvid))
                        })
                        .collect_vec()
                }
            }
        })
    }
}

/// Environment used to map from [`rty::Var`] to a [`fixpoint::LocalVar`]. This only supports
/// mapping of [`rty::Var::Bound`] and [`rty::Var::Free`].
struct LocalVarEnv {
    local_var_gen: IndexGen<fixpoint::LocalVar>,
    fvars: UnordMap<rty::Name, fixpoint::LocalVar>,
    /// Layers of late bound variables
    layers: Vec<Vec<fixpoint::LocalVar>>,
}

impl LocalVarEnv {
    fn new() -> Self {
        Self { local_var_gen: IndexGen::new(), fvars: Default::default(), layers: Vec::new() }
    }

    // This doesn't require to be mutable because `IndexGen` uses atomics, but we make it mutable
    // to better declare the intent.
    fn fresh_name(&mut self) -> fixpoint::LocalVar {
        self.local_var_gen.fresh()
    }

    fn insert_fvar_map(&mut self, name: rty::Name) -> fixpoint::LocalVar {
        let fresh = self.fresh_name();
        self.fvars.insert(name, fresh);
        fresh
    }

    fn remove_fvar_map(&mut self, name: rty::Name) {
        self.fvars.remove(&name);
    }

    /// Push a layer of bound variables assigning a fresh [`fixpoint::LocalVar`] to each one
    fn push_layer_with_fresh_names(&mut self, count: usize) {
        let layer = (0..count).map(|_| self.fresh_name()).collect();
        self.layers.push(layer);
    }

    fn pop_layer(&mut self) -> Vec<fixpoint::LocalVar> {
        self.layers.pop().unwrap()
    }

    fn get_fvar(&self, name: rty::Name) -> Option<fixpoint::LocalVar> {
        self.fvars.get(&name).copied()
    }

    fn get_late_bvar(&self, debruijn: DebruijnIndex, var: BoundVar) -> Option<fixpoint::LocalVar> {
        let depth = self.layers.len().checked_sub(debruijn.as_usize() + 1)?;
        self.layers[depth].get(var.as_usize()).copied()
    }
}

struct ConstInfo {
    name: fixpoint::GlobalVar,
    orig: String,
    sort: fixpoint::Sort,
    val: Option<Constant>,
}

impl FixpointKVar {
    fn new(sorts: Vec<fixpoint::Sort>, orig: rty::KVid) -> Self {
        Self { sorts, orig }
    }
}

pub struct KVarGen {
    kvars: IndexVec<rty::KVid, KVarDecl>,
    /// If true generate dummy [holes] instead of kvars. Used during shape mode to avoid generating
    /// unnecessary kvars.
    ///
    /// [holes]: rty::ExprKind::Hole
    dummy: bool,
}

impl KVarGen {
    pub fn new() -> Self {
        Self { kvars: IndexVec::new(), dummy: false }
    }

    pub fn dummy() -> Self {
        Self { kvars: IndexVec::new(), dummy: true }
    }

    fn get(&self, kvid: rty::KVid) -> &KVarDecl {
        &self.kvars[kvid]
    }

    /// Generate a fresh [kvar] under several layers of [binders]. The variables bound in the last
    /// layer (last element of the `binders` slice) are used as the self arguments. The rest of the
    /// binders are appended to the `scope`.
    ///
    /// Note that the returned expression will have escaping variables and it is up to the caller to
    /// put it under an appropriate number of binders.
    ///
    /// Prefer using [`InferCtxt::fresh_kvar`] when possible.
    ///
    /// [binders]: rty::Binder
    /// [kvar]: rty::KVar
    /// [`InferCtxt::fresh_kvar`]: crate::infer::InferCtxt::fresh_kvar
    pub fn fresh(
        &mut self,
        binders: &[List<rty::Sort>],
        scope: impl IntoIterator<Item = (rty::Var, rty::Sort)>,
        encoding: KVarEncoding,
    ) -> rty::Expr {
        if self.dummy {
            return rty::Expr::hole(rty::HoleKind::Pred);
        }

        if binders.is_empty() {
            return self.fresh_inner(0, [], encoding);
        }
        let args = itertools::chain(
            binders.iter().rev().enumerate().flat_map(|(level, sorts)| {
                let debruijn = DebruijnIndex::from_usize(level);
                sorts.iter().cloned().enumerate().map(move |(idx, sort)| {
                    let var = rty::BoundReft {
                        var: BoundVar::from_usize(idx),
                        kind: rty::BoundReftKind::Annon,
                    };
                    (rty::Var::Bound(debruijn, var), sort)
                })
            }),
            scope,
        );
        self.fresh_inner(binders.last().unwrap().len(), args, encoding)
    }

    fn fresh_inner<A>(&mut self, self_args: usize, args: A, encoding: KVarEncoding) -> rty::Expr
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
                if !matches!(sort, rty::Sort::Loc) {
                    flattened_self_args += is_self_arg as usize;
                    sorts.push(sort.clone());
                    exprs.push(rty::Expr::field_projs(&var, proj));
                }
            });
        }

        let kvid = self
            .kvars
            .push(KVarDecl { self_args: flattened_self_args, sorts, encoding });

        let kvar = rty::KVar::new(kvid, flattened_self_args, exprs);
        rty::Expr::kvar(kvar)
    }
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
    /// Generate a conjunction of kvars, one per argument in [`rty::KVar::args`].
    /// Concretely, a kvar `$k(a0, a1, ..., an)[b0, ...]` becomes
    /// `$k0(a0, a1, ..., an, b0, ...) ∧ $k1(a1, ..., an, b0, ...) ∧ ... ∧ $kn(an, b0, ...)`
    Conj,
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

struct ExprEncodingCtxt<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    local_var_env: LocalVarEnv,
    global_var_gen: IndexGen<fixpoint::GlobalVar>,
    const_map: ConstMap<'tcx>,
    errors: Errors<'genv>,
    def_span: Span,
}

impl<'genv, 'tcx> ExprEncodingCtxt<'genv, 'tcx> {
    fn new(genv: GlobalEnv<'genv, 'tcx>, def_span: Span) -> Self {
        Self {
            genv,
            local_var_env: LocalVarEnv::new(),
            global_var_gen: IndexGen::new(),
            const_map: Default::default(),
            errors: Errors::new(genv.sess()),
            def_span,
        }
    }

    fn var_to_fixpoint(&self, var: &rty::Var) -> fixpoint::Var {
        match var {
            rty::Var::Free(name) => {
                self.local_var_env
                    .get_fvar(*name)
                    .unwrap_or_else(|| {
                        span_bug!(self.def_span, "no entry found for name: `{name:?}`")
                    })
                    .into()
            }
            rty::Var::Bound(debruijn, breft) => {
                self.local_var_env
                    .get_late_bvar(*debruijn, breft.var)
                    .unwrap_or_else(|| {
                        span_bug!(self.def_span, "no entry found for late bound var: `{breft:?}`")
                    })
                    .into()
            }
            rty::Var::ConstGeneric(param) => fixpoint::Var::ConstGeneric(*param),
            rty::Var::EarlyParam(param) => fixpoint::Var::Param(*param),
            rty::Var::EVar(_) => {
                span_bug!(self.def_span, "unexpected evar: `{var:?}`")
            }
        }
    }

    fn expr_to_fixpoint(
        &mut self,
        expr: &rty::Expr,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        let e = match expr.kind() {
            rty::ExprKind::Var(var) => fixpoint::Expr::Var(self.var_to_fixpoint(var)),
            rty::ExprKind::Constant(c) => fixpoint::Expr::Constant(*c),
            rty::ExprKind::BinaryOp(op, e1, e2) => self.bin_op_to_fixpoint(op, e1, e2, scx)?,
            rty::ExprKind::UnaryOp(op, e) => self.un_op_to_fixpoint(*op, e, scx)?,
            rty::ExprKind::FieldProj(e, proj) => {
                let (arity, field) = match *proj {
                    rty::FieldProj::Tuple { arity, field } => (arity, field),
                    rty::FieldProj::Adt { def_id, field } => {
                        let arity = self.genv.adt_sort_def_of(def_id)?.fields();
                        (arity, field)
                    }
                };
                scx.declare_tuple(arity);
                let proj = fixpoint::Var::TupleProj { arity, field };
                fixpoint::Expr::App(proj, vec![self.expr_to_fixpoint(e, scx)?])
            }
            rty::ExprKind::Aggregate(_, flds) => {
                scx.declare_tuple(flds.len());
                let ctor = fixpoint::Var::TupleCtor { arity: flds.len() };
                let args = flds
                    .iter()
                    .map(|e| self.expr_to_fixpoint(e, scx))
                    .try_collect()?;
                fixpoint::Expr::App(ctor, args)
            }
            rty::ExprKind::ConstDefId(did) => {
                let var = self.register_rust_const(*did);
                fixpoint::Expr::Var(var.into())
            }
            rty::ExprKind::App(func, args) => {
                let func = self.func_to_fixpoint(func, scx);
                let args = self.exprs_to_fixpoint(args, scx)?;
                fixpoint::Expr::App(func, args)
            }
            rty::ExprKind::IfThenElse(p, e1, e2) => {
                fixpoint::Expr::IfThenElse(Box::new([
                    self.expr_to_fixpoint(p, scx)?,
                    self.expr_to_fixpoint(e1, scx)?,
                    self.expr_to_fixpoint(e2, scx)?,
                ]))
            }
            rty::ExprKind::Alias(alias_pred, args) => {
                let sort = self
                    .genv
                    .sort_of_assoc_reft(alias_pred.trait_id, alias_pred.name)?
                    .unwrap();
                let sort = sort.instantiate_identity(&[]);
                let func = self.register_const_for_alias_reft(alias_pred, sort, scx);
                let args = args
                    .iter()
                    .map(|expr| self.expr_to_fixpoint(expr, scx))
                    .try_collect()?;
                fixpoint::Expr::App(func.into(), args)
            }
            rty::ExprKind::Abs(lam) => {
                let var = self.register_const_for_lambda(lam, scx);
                fixpoint::Expr::Var(var.into())
            }
            rty::ExprKind::Hole(..)
            | rty::ExprKind::KVar(_)
            | rty::ExprKind::Local(_)
            | rty::ExprKind::GlobalFunc(..)
            | rty::ExprKind::PathProj(..)
            | rty::ExprKind::ForAll(_) => {
                span_bug!(self.def_span, "unexpected expr: `{expr:?}`")
            }
        };
        Ok(e)
    }

    fn exprs_to_fixpoint<'b>(
        &mut self,
        exprs: impl IntoIterator<Item = &'b rty::Expr>,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<Vec<fixpoint::Expr>> {
        exprs
            .into_iter()
            .map(|e| self.expr_to_fixpoint(e, scx))
            .try_collect()
    }

    fn un_op_to_fixpoint(
        &mut self,
        op: rty::UnOp,
        e: &rty::Expr,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        match op {
            rty::UnOp::Not => Ok(fixpoint::Expr::Not(Box::new(self.expr_to_fixpoint(e, scx)?))),
            rty::UnOp::Neg => Ok(fixpoint::Expr::Neg(Box::new(self.expr_to_fixpoint(e, scx)?))),
        }
    }

    fn bin_op_to_fixpoint(
        &mut self,
        op: &rty::BinOp,
        e1: &rty::Expr,
        e2: &rty::Expr,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        let op = match op {
            rty::BinOp::Eq => {
                return Ok(fixpoint::Expr::Atom(
                    fixpoint::BinRel::Eq,
                    Box::new([self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?]),
                ))
            }
            rty::BinOp::Ne => {
                return Ok(fixpoint::Expr::Atom(
                    fixpoint::BinRel::Ne,
                    Box::new([self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?]),
                ))
            }
            rty::BinOp::Gt(sort) => {
                return self.bin_rel_to_fixpoint(sort, fixpoint::BinRel::Gt, e1, e2, scx);
            }
            rty::BinOp::Ge(sort) => {
                return self.bin_rel_to_fixpoint(sort, fixpoint::BinRel::Ge, e1, e2, scx);
            }
            rty::BinOp::Lt(sort) => {
                return self.bin_rel_to_fixpoint(sort, fixpoint::BinRel::Lt, e1, e2, scx);
            }
            rty::BinOp::Le(sort) => {
                return self.bin_rel_to_fixpoint(sort, fixpoint::BinRel::Le, e1, e2, scx);
            }
            rty::BinOp::And => {
                return Ok(fixpoint::Expr::And(vec![
                    self.expr_to_fixpoint(e1, scx)?,
                    self.expr_to_fixpoint(e2, scx)?,
                ]))
            }
            rty::BinOp::Or => {
                return Ok(fixpoint::Expr::Or(vec![
                    self.expr_to_fixpoint(e1, scx)?,
                    self.expr_to_fixpoint(e2, scx)?,
                ]))
            }
            rty::BinOp::Imp => {
                return Ok(fixpoint::Expr::Imp(Box::new([
                    self.expr_to_fixpoint(e1, scx)?,
                    self.expr_to_fixpoint(e2, scx)?,
                ])))
            }
            rty::BinOp::Iff => {
                return Ok(fixpoint::Expr::Iff(Box::new([
                    self.expr_to_fixpoint(e1, scx)?,
                    self.expr_to_fixpoint(e2, scx)?,
                ])))
            }
            rty::BinOp::Add => fixpoint::BinOp::Add,
            rty::BinOp::Sub => fixpoint::BinOp::Sub,
            rty::BinOp::Mul => fixpoint::BinOp::Mul,
            rty::BinOp::Div => fixpoint::BinOp::Div,
            rty::BinOp::Mod => fixpoint::BinOp::Mod,
        };
        Ok(fixpoint::Expr::BinaryOp(
            op,
            Box::new([self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?]),
        ))
    }

    /// A binary relation is encoded as a structurally recursive relation between aggregate sorts.
    /// For "leaf" expressions, we encode them as an interpreted relation if the sort supports it,
    /// otherwise we use an uninterpreted function. For example, consider the following relation
    /// between two tuples of sort `(int, int -> int)`
    /// ```text
    /// (0, λv. v + 1) <= (1, λv. v + 1)
    /// ```
    /// The encoding in fixpoint will be
    ///
    /// ```text
    /// 0 <= 1 && (le (λv. v + 1) (λv. v + 1))
    /// ```
    /// Where `<=` is the (interpreted) less than or equal relation between integers and `le` is
    /// an uninterpreted relation between ([the encoding] of) lambdas.
    ///
    /// [the encoding]: Self::register_const_for_lambda
    fn bin_rel_to_fixpoint(
        &mut self,
        sort: &rty::Sort,
        rel: fixpoint::BinRel,
        e1: &rty::Expr,
        e2: &rty::Expr,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        let e = match sort {
            rty::Sort::Int | rty::Sort::Real => {
                fixpoint::Expr::Atom(
                    rel,
                    Box::new([self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?]),
                )
            }
            rty::Sort::Tuple(sorts) => {
                let arity = sorts.len();
                self.apply_bin_rel_rec(sorts, rel, e1, e2, scx, |field| {
                    rty::FieldProj::Tuple { arity, field }
                })?
            }
            rty::Sort::App(rty::SortCtor::Adt(sort_def), args) => {
                let def_id = sort_def.did();
                let sorts = sort_def.field_sorts(args);
                self.apply_bin_rel_rec(&sorts, rel, e1, e2, scx, |field| {
                    rty::FieldProj::Adt { def_id, field }
                })?
            }
            _ => {
                let rel = fixpoint::Var::UIFRel(rel);
                fixpoint::Expr::App(
                    rel,
                    vec![self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?],
                )
            }
        };
        Ok(e)
    }

    /// Apply binary relation recursively over aggregate expessions
    fn apply_bin_rel_rec(
        &mut self,
        sorts: &[rty::Sort],
        rel: fixpoint::BinRel,
        e1: &rty::Expr,
        e2: &rty::Expr,
        scx: &mut SortEncodingCtxt,
        mk_proj: impl Fn(u32) -> rty::FieldProj,
    ) -> QueryResult<fixpoint::Expr> {
        Ok(fixpoint::Expr::And(
            sorts
                .iter()
                .enumerate()
                .map(|(idx, s)| {
                    let proj = mk_proj(idx as u32);
                    let e1 = e1.proj_and_reduce(proj);
                    let e2 = e2.proj_and_reduce(proj);
                    self.bin_rel_to_fixpoint(s, rel, &e1, &e2, scx)
                })
                .try_collect()?,
        ))
    }

    fn func_to_fixpoint(&mut self, func: &rty::Expr, scx: &mut SortEncodingCtxt) -> fixpoint::Var {
        match func.kind() {
            rty::ExprKind::Var(var) => self.var_to_fixpoint(var),
            rty::ExprKind::GlobalFunc(_, SpecFuncKind::Thy(sym)) => fixpoint::Var::Itf(*sym),
            rty::ExprKind::GlobalFunc(sym, SpecFuncKind::Uif) => {
                self.register_uif(*sym, scx).into()
            }
            rty::ExprKind::GlobalFunc(sym, SpecFuncKind::Def) => {
                span_bug!(self.def_span, "unexpected global function `{sym}`. Function must be normalized away at this point")
            }
            _ => {
                span_bug!(self.def_span, "unexpected expr `{func:?}` in function position")
            }
        }
    }

    fn imm(
        &mut self,
        arg: &rty::Expr,
        sort: &rty::Sort,
        scx: &mut SortEncodingCtxt,
        bindings: &mut Vec<fixpoint::Bind>,
    ) -> QueryResult<fixpoint::Var> {
        match arg.kind() {
            rty::ExprKind::Var(var) => Ok(self.var_to_fixpoint(var)),
            _ => {
                let fresh = self.local_var_env.fresh_name();
                let pred = fixpoint::Expr::eq(
                    fixpoint::Expr::Var(fresh.into()),
                    self.expr_to_fixpoint(arg, scx)?,
                );
                bindings.push(fixpoint::Bind {
                    name: fresh.into(),
                    sort: scx.sort_to_fixpoint(sort),
                    pred: fixpoint::Pred::Expr(pred),
                });
                Ok(fresh.into())
            }
        }
    }

    fn register_uif(&mut self, name: Symbol, scx: &mut SortEncodingCtxt) -> fixpoint::GlobalVar {
        let key = Key::Uif(name);
        self.const_map
            .entry(key)
            .or_insert_with(|| {
                let sort = self
                    .genv
                    .func_decl(name)
                    .map(|decl| {
                        debug_assert_eq!(decl.kind, fhir::SpecFuncKind::Uif);
                        scx.func_sort_to_fixpoint(&decl.sort)
                    })
                    .unwrap_or_else(|err| {
                        self.errors.emit(err.at(self.def_span));
                        fixpoint::Sort::Int
                    });
                ConstInfo {
                    name: self.global_var_gen.fresh(),
                    orig: name.to_string(),
                    sort,
                    val: None,
                }
            })
            .name
    }

    fn register_rust_const(&mut self, def_id: DefId) -> fixpoint::GlobalVar {
        let key = Key::Const(def_id);
        self.const_map
            .entry(key)
            .or_insert_with(|| {
                // TODO(nilehmann) generalize const sorts
                let ty = self.genv.tcx().type_of(def_id).no_bound_vars().unwrap();
                assert!(ty.is_integral());

                // FIXME(nilehmann) we should probably report an error in case const evaluation
                // fails instead of silently ignore it.
                let val = self
                    .genv
                    .tcx()
                    .const_eval_poly(def_id)
                    .ok()
                    .and_then(|val| {
                        let val = val.try_to_scalar_int()?;
                        const_eval::scalar_int_to_rty_constant(self.genv.tcx(), val, ty)
                    });

                ConstInfo {
                    name: self.global_var_gen.fresh(),
                    orig: pretty::def_id_to_string(def_id),
                    sort: fixpoint::Sort::Int,
                    val,
                }
            })
            .name
    }

    /// returns the 'constant' UIF for Var used to represent the alias_pred, creating and adding it
    /// to the const_map if necessary
    fn register_const_for_alias_reft(
        &mut self,
        alias_reft: &rty::AliasReft,
        fsort: rty::FuncSort,
        scx: &mut SortEncodingCtxt,
    ) -> fixpoint::GlobalVar {
        let key = Key::Alias(alias_reft.to_rustc_trait_ref(self.genv.tcx()));
        self.const_map
            .entry(key)
            .or_insert_with(|| {
                let orig = format!("{alias_reft:?}");
                let name = self.global_var_gen.fresh();
                let fsort = rty::PolyFuncSort::new(List::empty(), fsort);
                let sort = scx.func_sort_to_fixpoint(&fsort);
                ConstInfo { name, orig, sort, val: None }
            })
            .name
    }

    /// We encode lambdas with uninterpreted constant. Two syntactically equal lambdas will be encoded
    /// with the same constant.
    fn register_const_for_lambda(
        &mut self,
        lam: &rty::Lambda,

        scx: &mut SortEncodingCtxt,
    ) -> fixpoint::GlobalVar {
        let key = Key::Lambda(lam.clone());
        self.const_map
            .entry(key)
            .or_insert_with(|| {
                let orig = format!("{lam:?}");
                let name = self.global_var_gen.fresh();
                let sort = scx.func_sort_to_fixpoint(&lam.sort().to_poly());
                ConstInfo { name, orig, sort, val: None }
            })
            .name
    }

    fn qualifier_to_fixpoint(
        &mut self,
        qualifier: &rty::Qualifier,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Qualifier> {
        self.local_var_env
            .push_layer_with_fresh_names(qualifier.body.vars().len());
        let body = self.expr_to_fixpoint(qualifier.body.as_ref().skip_binder(), scx)?;

        let args: Vec<(fixpoint::Var, fixpoint::Sort)> =
            iter::zip(self.local_var_env.pop_layer(), qualifier.body.vars())
                .map(|(name, var)| (name.into(), scx.sort_to_fixpoint(var.expect_sort())))
                .collect();

        let name = qualifier.name.to_string();

        Ok(fixpoint::Qualifier { name, args, body })
    }
}

fn mk_implies(assumption: fixpoint::Pred, cstr: fixpoint::Constraint) -> fixpoint::Constraint {
    fixpoint::Constraint::ForAll(
        fixpoint::Bind {
            name: fixpoint::Var::Underscore,
            sort: fixpoint::Sort::Int,
            pred: assumption,
        },
        Box::new(cstr),
    )
}
