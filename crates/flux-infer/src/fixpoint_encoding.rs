//! Encoding of the refinement tree into a fixpoint constraint.

use std::{collections::HashMap, hash::Hash, iter};

use fixpoint::AdtId;
use flux_common::{
    bug,
    cache::QueryCache,
    dbg,
    index::{IndexGen, IndexVec},
    iter::IterExt,
    span_bug, tracked_span_bug,
};
use flux_config::{self as config};
use flux_errors::Errors;
use flux_middle::{
    FixpointQueryKind,
    def_id::{FluxDefId, MaybeExternId},
    def_id_to_string,
    global_env::GlobalEnv,
    queries::QueryResult,
    rty::{self, ESpan, GenericArgsExt, InternalFuncKind, Lambda, List, SpecFuncKind, VariantIdx},
    timings::{self, TimingKind},
};
use itertools::Itertools;
use liquid_fixpoint::{FixpointStatus, SmtSolver};
use rustc_data_structures::{
    fx::{FxIndexMap, FxIndexSet},
    unord::{UnordMap, UnordSet},
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::newtype_index;
use rustc_infer::infer::TyCtxtInferExt as _;
use rustc_middle::ty::TypingMode;
use rustc_span::Span;
use rustc_type_ir::{BoundVar, DebruijnIndex};
use serde::{Deserialize, Deserializer, Serialize};

use crate::{
    fixpoint_qualifiers::FIXPOINT_QUALIFIERS, lean_encoding::LeanEncoder,
    projections::structurally_normalize_expr,
};

pub mod decoding;

pub mod fixpoint {
    use std::fmt;

    use flux_middle::rty::EarlyReftParam;
    use liquid_fixpoint::{FixpointFmt, Identifier};
    use rustc_abi::VariantIdx;
    use rustc_index::newtype_index;
    use rustc_middle::ty::ParamConst;
    use rustc_span::Symbol;

    newtype_index! {
        pub struct KVid {}
    }

    impl Identifier for KVid {
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

    newtype_index! {
        /// Unique id assigned to each [`flux_middle::rty::AdtSortDef`] that needs to be encoded
        /// into fixpoint
        pub struct AdtId {}
    }

    #[derive(Hash, Copy, Clone, Debug, PartialEq, Eq)]
    pub enum Var {
        Underscore,
        Global(GlobalVar, Option<Symbol>),
        Local(LocalVar),
        DataCtor(AdtId, VariantIdx),
        TupleCtor { arity: usize },
        TupleProj { arity: usize, field: u32 },
        DataProj { adt_id: AdtId, /* variant_idx: VariantIdx, */ field: u32 },
        UIFRel(BinRel),
        Param(EarlyReftParam),
        ConstGeneric(ParamConst),
    }

    impl From<GlobalVar> for Var {
        fn from(v: GlobalVar) -> Self {
            Self::Global(v, None)
        }
    }

    impl From<LocalVar> for Var {
        fn from(v: LocalVar) -> Self {
            Self::Local(v)
        }
    }

    impl Identifier for Var {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Var::Global(v, None) => write!(f, "c{}", v.as_u32()),
                Var::Global(v, Some(sym)) => write!(f, "f${}${}", sym, v.as_u32()),
                Var::Local(v) => write!(f, "a{}", v.as_u32()),
                Var::DataCtor(adt_id, variant_idx) => {
                    write!(f, "mkadt{}${}", adt_id.as_u32(), variant_idx.as_u32())
                }
                Var::TupleCtor { arity } => write!(f, "mktuple{arity}"),
                Var::TupleProj { arity, field } => write!(f, "tuple{arity}${field}"),
                Var::DataProj { adt_id, field } => write!(f, "fld{}${field}", adt_id.as_u32()),
                Var::UIFRel(BinRel::Gt) => write!(f, "gt"),
                Var::UIFRel(BinRel::Ge) => write!(f, "ge"),
                Var::UIFRel(BinRel::Lt) => write!(f, "lt"),
                Var::UIFRel(BinRel::Le) => write!(f, "le"),
                // these are actually not necessary because equality is interpreted for all sorts
                Var::UIFRel(BinRel::Eq) => write!(f, "eq"),
                Var::UIFRel(BinRel::Ne) => write!(f, "ne"),
                Var::Underscore => write!(f, "_$"), // To avoid clashing with `_` used for `app (_ bv_op n)` for parametric SMT ops
                Var::ConstGeneric(param) => {
                    write!(f, "constgen${}${}", param.name, param.index)
                }
                Var::Param(param) => {
                    write!(f, "reftgen${}${}", param.name, param.index)
                }
            }
        }
    }

    #[derive(Clone, Hash, Debug, PartialEq, Eq)]
    pub enum DataSort {
        Tuple(usize),
        Adt(AdtId),
    }

    impl Identifier for DataSort {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                DataSort::Tuple(arity) => {
                    write!(f, "Tuple{arity}")
                }
                DataSort::Adt(adt_id) => {
                    write!(f, "Adt{}", adt_id.as_u32())
                }
            }
        }
    }

    #[derive(Hash, Clone, Debug)]
    pub struct SymStr(pub Symbol);

    #[cfg(feature = "rust-fixpoint")]
    impl FixpointFmt for SymStr {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    #[cfg(not(feature = "rust-fixpoint"))]
    impl FixpointFmt for SymStr {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "\"{}\"", self.0)
        }
    }

    liquid_fixpoint::declare_types! {
        type Sort = DataSort;
        type KVar = KVid;
        type Var = Var;
        type String = SymStr;
        type Tag = super::TagIdx;
    }
    pub use fixpoint_generated::*;
}

newtype_index! {
    #[debug_format = "TagIdx({})"]
    pub struct TagIdx {}
}

impl Serialize for TagIdx {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_u32().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for TagIdx {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let idx = usize::deserialize(deserializer)?;
        Ok(TagIdx::from_u32(idx as u32))
    }
}

/// Keep track of all the data sorts that we need to define in fixpoint to encode the constraint.
#[derive(Default)]
struct SortEncodingCtxt {
    /// Set of all the tuple arities that need to be defined
    tuples: UnordSet<usize>,
    /// Set of all the [`AdtDefSortDef`](flux_middle::rty::AdtSortDef) that need to be declared as
    /// Fixpoint data-decls
    adt_sorts: FxIndexSet<DefId>,
}

impl SortEncodingCtxt {
    fn sort_to_fixpoint(&mut self, sort: &rty::Sort) -> fixpoint::Sort {
        match sort {
            rty::Sort::Int => fixpoint::Sort::Int,
            rty::Sort::Real => fixpoint::Sort::Real,
            rty::Sort::Bool => fixpoint::Sort::Bool,
            rty::Sort::Str => fixpoint::Sort::Str,
            rty::Sort::Char => fixpoint::Sort::Int,
            rty::Sort::BitVec(size) => fixpoint::Sort::BitVec(Box::new(bv_size_to_fixpoint(*size))),
            // There's no way to declare opaque sorts in the fixpoint horn syntax so we encode user
            // declared opaque sorts, type parameter sorts, and (unormalizable) type alias sorts as
            // integers. Well-formedness should ensure values of these sorts are used "opaquely",
            // i.e., the only values of these sorts are variables.
            rty::Sort::App(rty::SortCtor::User { .. }, _)
            | rty::Sort::Param(_)
            | rty::Sort::Alias(rty::AliasKind::Opaque | rty::AliasKind::Projection, ..) => {
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
                if let Some(variant) = sort_def.opt_struct_variant() {
                    let sorts = variant.field_sorts(args);
                    // do not generate 1-tuples
                    if let [sort] = &sorts[..] {
                        self.sort_to_fixpoint(sort)
                    } else {
                        let adt_id = self.declare_adt(sort_def.did());
                        let ctor = fixpoint::SortCtor::Data(fixpoint::DataSort::Adt(adt_id));
                        let args = args.iter().map(|s| self.sort_to_fixpoint(s)).collect_vec();
                        fixpoint::Sort::App(ctor, args)
                    }
                } else {
                    debug_assert!(args.is_empty());
                    let adt_id = self.declare_adt(sort_def.did());
                    fixpoint::Sort::App(
                        fixpoint::SortCtor::Data(fixpoint::DataSort::Adt(adt_id)),
                        vec![],
                    )
                }
            }
            rty::Sort::Tuple(sorts) => {
                // do not generate 1-tuples
                if let [sort] = &sorts[..] {
                    self.sort_to_fixpoint(sort)
                } else {
                    self.declare_tuple(sorts.len());
                    let ctor = fixpoint::SortCtor::Data(fixpoint::DataSort::Tuple(sorts.len()));
                    let args = sorts.iter().map(|s| self.sort_to_fixpoint(s)).collect();
                    fixpoint::Sort::App(ctor, args)
                }
            }
            rty::Sort::Func(sort) => self.func_sort_to_fixpoint(sort),
            rty::Sort::Var(k) => fixpoint::Sort::Var(k.index()),
            rty::Sort::Err
            | rty::Sort::Infer(_)
            | rty::Sort::Loc
            | rty::Sort::Alias(rty::AliasKind::Free, _) => {
                tracked_span_bug!("unexpected sort `{sort:?}`")
            }
        }
    }

    fn func_sort_to_fixpoint(&mut self, fsort: &rty::PolyFuncSort) -> fixpoint::Sort {
        let params = fsort.params().len();
        let fsort = fsort.skip_binders();
        let output = self.sort_to_fixpoint(fsort.output());
        fixpoint::Sort::mk_func(
            params,
            fsort.inputs().iter().map(|s| self.sort_to_fixpoint(s)),
            output,
        )
    }

    fn declare_tuple(&mut self, arity: usize) {
        self.tuples.insert(arity);
    }

    pub fn declare_adt(&mut self, did: DefId) -> AdtId {
        if let Some(idx) = self.adt_sorts.get_index_of(&did) {
            AdtId::from_usize(idx)
        } else {
            let adt_id = AdtId::from_usize(self.adt_sorts.len());
            self.adt_sorts.insert(did);
            adt_id
        }
    }

    fn append_adt_decls(
        &mut self,
        genv: GlobalEnv,
        decls: &mut Vec<fixpoint::DataDecl>,
    ) -> QueryResult {
        // We iterate until we have processed all adt sorts because processing one adt sort may
        // discover new adt sorts to process (e.g., if an adt field has an adt sort).
        let mut idx = 0;
        while let Some(adt_def_id) = self.adt_sorts.get_index(idx) {
            let adt_id = AdtId::from_usize(idx);
            let adt_sort_def = genv.adt_sort_def_of(adt_def_id)?;
            decls.push(fixpoint::DataDecl {
                name: fixpoint::DataSort::Adt(adt_id),
                vars: adt_sort_def.param_count(),
                ctors: adt_sort_def
                    .variants()
                    .iter_enumerated()
                    .map(|(idx, variant)| {
                        let name = fixpoint::Var::DataCtor(adt_id, idx);
                        let fields = variant
                            .field_sorts_instantiate_identity()
                            .iter()
                            .enumerate()
                            .map(|(i, sort)| {
                                fixpoint::DataField {
                                    name: fixpoint::Var::DataProj { adt_id, field: i as u32 },
                                    sort: self.sort_to_fixpoint(sort),
                                }
                            })
                            .collect_vec();
                        fixpoint::DataCtor { name, fields }
                    })
                    .collect(),
            });
            idx += 1;
        }
        Ok(())
    }

    fn append_tuple_decls(tuples: UnordSet<usize>, decls: &mut Vec<fixpoint::DataDecl>) {
        decls.extend(
            tuples
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
                }),
        );
    }

    fn into_data_decls(mut self, genv: GlobalEnv) -> QueryResult<Vec<fixpoint::DataDecl>> {
        let mut decls = vec![];
        self.append_adt_decls(genv, &mut decls)?;
        Self::append_tuple_decls(self.tuples, &mut decls);
        Ok(decls)
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

type FunDefMap = FxIndexMap<FluxDefId, fixpoint::Var>;
type ConstMap<'tcx> = FxIndexMap<ConstKey<'tcx>, fixpoint::ConstDecl>;

#[derive(Eq, Hash, PartialEq, Clone)]
enum ConstKey<'tcx> {
    Uif(FluxDefId),
    RustConst(DefId),
    Alias(FluxDefId, rustc_middle::ty::GenericArgsRef<'tcx>),
    Lambda(Lambda),
    PrimOp(rty::BinOp),
    Cast(rty::Sort, rty::Sort),
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
}

pub type FixQueryCache = QueryCache<FixpointStatus<TagIdx>>;

impl<'genv, 'tcx, Tag> FixpointCtxt<'genv, 'tcx, Tag>
where
    Tag: std::hash::Hash + Eq + Copy,
{
    pub fn new(genv: GlobalEnv<'genv, 'tcx>, def_id: MaybeExternId, kvars: KVarGen) -> Self {
        Self {
            comments: vec![],
            kvars,
            scx: SortEncodingCtxt::default(),
            genv,
            ecx: ExprEncodingCtxt::new(genv, def_id),
            kcx: Default::default(),
            tags: IndexVec::new(),
            tags_inv: Default::default(),
        }
    }

    pub fn check(
        mut self,
        cache: &mut FixQueryCache,
        constraint: fixpoint::Constraint,
        kind: FixpointQueryKind,
        scrape_quals: bool,
        solver: SmtSolver,
    ) -> QueryResult<Vec<Tag>> {
        // skip checking trivial constraints
        if !constraint.is_concrete() {
            self.ecx.errors.into_result()?;
            return Ok(vec![]);
        }
        let def_span = self.ecx.def_span();
        let def_id = self.ecx.def_id;

        let kvars = self.kcx.into_fixpoint();

        let (define_funs, define_constants) = self.ecx.define_funs(def_id, &mut self.scx)?;
        let qualifiers = self
            .ecx
            .qualifiers_for(def_id.local_id(), &mut self.scx)?
            .into_iter()
            .chain(FIXPOINT_QUALIFIERS.iter().cloned())
            .collect();

        // Assuming values should happen after all encoding is done so we are sure we've collected
        // all constants.
        let constraint = self.ecx.assume_const_values(constraint, &mut self.scx)?;

        let mut constants = self.ecx.const_env.const_map.into_values().collect_vec();
        constants.extend(define_constants);

        // The rust fixpoint implementation does not yet support polymorphic functions.
        // For now we avoid including these by default so that cases where they are not needed can work.
        // Should be removed when support is added.
        #[cfg(not(feature = "rust-fixpoint"))]
        for rel in fixpoint::BinRel::INEQUALITIES {
            // ∀a. a -> a -> bool
            let sort = fixpoint::Sort::mk_func(
                1,
                [fixpoint::Sort::Var(0), fixpoint::Sort::Var(0)],
                fixpoint::Sort::Bool,
            );
            constants.push(fixpoint::ConstDecl {
                name: fixpoint::Var::UIFRel(rel),
                sort,
                comment: None,
            });
        }

        // We are done encoding expressions. Check if there are any errors.
        self.ecx.errors.into_result()?;

        let task = fixpoint::Task {
            comments: self.comments,
            constants,
            kvars,
            define_funs,
            constraint,
            qualifiers,
            scrape_quals,
            solver,
            data_decls: self.scx.into_data_decls(self.genv)?,
        };
        if config::dump_constraint() {
            dbg::dump_item_info(self.genv.tcx(), def_id.resolved_id(), "smt2", &task).unwrap();
        }

        match Self::run_task_with_cache(self.genv, task, def_id.resolved_id(), kind, cache) {
            FixpointStatus::Safe(_) => Ok(vec![]),
            FixpointStatus::Unsafe(_, errors) => {
                Ok(errors
                    .into_iter()
                    .map(|err| self.tags[err.tag])
                    .unique()
                    .collect_vec())
            }
            FixpointStatus::Crash(err) => span_bug!(def_span, "fixpoint crash: {err:?}"),
        }
    }

    pub fn generate_and_check_lean_lemmas(
        mut self,
        constraint: fixpoint::Constraint,
    ) -> QueryResult<()> {
        let def_id = self.ecx.def_id;

        if !self.kcx.into_fixpoint().is_empty() {
            tracked_span_bug!("cannot generate lean lemmas for constraints with kvars");
        }

        let (define_funs, define_constants) = self.ecx.define_funs(def_id, &mut self.scx)?;

        let constraint = self.ecx.assume_const_values(constraint, &mut self.scx)?;

        let mut constants = self.ecx.const_env.const_map.into_values().collect_vec();
        constants.extend(define_constants);

        self.ecx.errors.into_result()?;

        let lean_encoder = LeanEncoder::new(def_id, self.genv, define_funs, constants, constraint);
        let lean_path = std::path::Path::new("./");
        let project_name = "lean_proofs";
        lean_encoder.check_proof(lean_path, project_name)
    }

    fn run_task_with_cache(
        genv: GlobalEnv,
        task: fixpoint::Task,
        def_id: DefId,
        kind: FixpointQueryKind,
        cache: &mut FixQueryCache,
    ) -> FixpointStatus<TagIdx> {
        let key = kind.task_key(genv.tcx(), def_id);

        let hash = task.hash_with_default();

        if config::is_cache_enabled()
            && let Some(result) = cache.lookup(&key, hash)
        {
            return result.clone();
        }
        let result = timings::time_it(TimingKind::FixpointQuery(def_id, kind), || {
            task.run()
                .unwrap_or_else(|err| tracked_span_bug!("failed to run fixpoint: {err}"))
        });

        if config::is_cache_enabled() {
            cache.insert(key, hash, result.status.clone());
        }

        println!("TRACE: fixpoint solution");
        for b in &result.solution {
            println!("{}", b.dump());
        }
        println!("TRACE: fixpoint non-cut solution");
        for b in &result.non_cuts_solution {
            println!("{}", b.dump());
        }

        result.status
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

    pub(crate) fn sort_to_fixpoint(&mut self, sort: &rty::Sort) -> fixpoint::Sort {
        self.scx.sort_to_fixpoint(sort)
    }

    pub(crate) fn var_to_fixpoint(&self, var: &rty::Var) -> fixpoint::Var {
        self.ecx.var_to_fixpoint(var)
    }

    /// Encodes an expression in head position as a [`fixpoint::Constraint`] "peeling out"
    /// implications and foralls.
    ///
    /// [`fixpoint::Constraint`]: liquid_fixpoint::Constraint
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
                Ok(fixpoint::Constraint::conj(cstrs))
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

                let bindings = iter::zip(vars, pred.vars())
                    .map(|(var, kind)| {
                        fixpoint::Bind {
                            name: var.into(),
                            sort: self.scx.sort_to_fixpoint(kind.expect_sort()),
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
    /// predicate and a list of bindings produced by ANF-ing kvars.
    ///
    /// [`fixpoint::Pred`]: liquid_fixpoint::Pred
    pub(crate) fn assumption_to_fixpoint(
        &mut self,
        pred: &rty::Expr,
    ) -> QueryResult<(Vec<fixpoint::Bind>, fixpoint::Pred)> {
        let mut bindings = vec![];
        let mut preds = vec![];
        self.assumption_to_fixpoint_aux(pred, &mut bindings, &mut preds)?;
        Ok((bindings, fixpoint::Pred::and(preds)))
    }

    /// Auxiliary function to merge nested conjunctions in a single predicate
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
                // because we are weakening the context, i.e., anything true without the assumption
                // should remain true after adding it. Note that this relies on the predicate
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
            .map(|(arg, sort)| self.ecx.imm(arg, sort, &mut self.scx, bindings))
            .try_collect_vec()?;

        // Fixpoint doesn't support kvars without arguments, which we do generate sometimes. To get
        // around it, we encode `$k()` as ($k 0), or more precisely `(forall ((x int) (= x 0)) ... ($k x)`
        // after ANF-ing.
        if all_args.is_empty() {
            let fresh = self.ecx.local_var_env.fresh_name();
            let var = fixpoint::Var::Local(fresh);
            bindings.push(fixpoint::Bind {
                name: fresh.into(),
                sort: fixpoint::Sort::Int,
                pred: fixpoint::Pred::Expr(fixpoint::Expr::eq(
                    fixpoint::Expr::Var(var),
                    fixpoint::Expr::int(0),
                )),
            });
            return Ok(fixpoint::Pred::KVar(kvids[0], vec![var]));
        }

        let kvars = kvids
            .iter()
            .enumerate()
            .map(|(i, kvid)| {
                let args = all_args[i..].to_vec();
                fixpoint::Pred::KVar(*kvid, args)
            })
            .collect_vec();

        Ok(fixpoint::Pred::And(kvars))
    }
}

fn const_to_fixpoint(cst: rty::Constant) -> fixpoint::Expr {
    match cst {
        rty::Constant::Int(i) => {
            if i.is_negative() {
                fixpoint::Expr::Neg(Box::new(fixpoint::Constant::Numeral(i.abs()).into()))
            } else {
                fixpoint::Constant::Numeral(i.abs()).into()
            }
        }
        rty::Constant::Real(r) => fixpoint::Constant::Real(r.0).into(),
        rty::Constant::Bool(b) => fixpoint::Constant::Boolean(b).into(),
        rty::Constant::Char(c) => fixpoint::Constant::Numeral(u128::from(c)).into(),
        rty::Constant::Str(s) => fixpoint::Constant::String(fixpoint::SymStr(s)).into(),
        rty::Constant::BitVec(i, size) => fixpoint::Constant::BitVec(i, size).into(),
    }
}

struct FixpointKVar {
    sorts: Vec<fixpoint::Sort>,
    orig: rty::KVid,
}

/// During encoding into fixpoint we generate multiple fixpoint kvars per kvar in flux. A
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
                            let sorts = all_args[i..].to_vec();
                            self.kvars.push(FixpointKVar::new(sorts, kvid))
                        })
                        .collect_vec()
                }
            }
        })
    }

    fn into_fixpoint(self) -> Vec<fixpoint::KVarDecl> {
        self.kvars
            .into_iter_enumerated()
            .map(|(kvid, kvar)| {
                fixpoint::KVarDecl::new(kvid, kvar.sorts, format!("orig: {:?}", kvar.orig))
            })
            .collect()
    }
}

/// Environment used to map from [`rty::Var`] to a [`fixpoint::LocalVar`].
struct LocalVarEnv {
    local_var_gen: IndexGen<fixpoint::LocalVar>,
    fvars: UnordMap<rty::Name, fixpoint::LocalVar>,
    /// Layers of late bound variables
    layers: Vec<Vec<fixpoint::LocalVar>>,
    reverse_map: UnordMap<fixpoint::LocalVar, rty::Var>,
}

impl LocalVarEnv {
    fn new() -> Self {
        Self {
            local_var_gen: IndexGen::new(),
            fvars: Default::default(),
            layers: Vec::new(),
            reverse_map: Default::default(),
        }
    }

    // This doesn't require to be mutable because `IndexGen` uses atomics, but we make it mutable
    // to better declare the intent.
    fn fresh_name(&mut self) -> fixpoint::LocalVar {
        self.local_var_gen.fresh()
    }

    fn insert_fvar_map(&mut self, name: rty::Name) -> fixpoint::LocalVar {
        let fresh = self.fresh_name();
        self.fvars.insert(name, fresh);
        self.reverse_map.insert(fresh, rty::Var::Free(name));
        fresh
    }

    fn remove_fvar_map(&mut self, name: rty::Name) {
        self.fvars.remove(&name);
    }

    /// Push a layer of bound variables assigning a fresh [`fixpoint::LocalVar`] to each one
    fn push_layer_with_fresh_names(&mut self, count: usize) {
        let layer = (0..count).map(|_| self.fresh_name()).collect();
        self.layers.push(layer);
        // FIXME: (ck) what to put in reverse_map here?
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

impl FixpointKVar {
    fn new(sorts: Vec<fixpoint::Sort>, orig: rty::KVid) -> Self {
        Self { sorts, orig }
    }
}

pub struct KVarGen {
    kvars: IndexVec<rty::KVid, KVarDecl>,
    /// If true, generate dummy [holes] instead of kvars. Used during shape mode to avoid generating
    /// unnecessary kvars.
    ///
    /// [holes]: rty::ExprKind::Hole
    dummy: bool,
}

impl KVarGen {
    pub(crate) fn new(dummy: bool) -> Self {
        Self { kvars: IndexVec::new(), dummy }
    }

    fn get(&self, kvid: rty::KVid) -> &KVarDecl {
        &self.kvars[kvid]
    }

    /// Generate a fresh [kvar] under several layers of [binders]. Each layer may contain any kind
    /// of bound variable, but variables that are not of kind [`BoundVariableKind::Refine`] will
    /// be filtered out.
    ///
    /// The variables bound in the last layer (last element of the `binders` slice) is expected to
    /// have only [`BoundVariableKind::Refine`] and all its elements are used as the [self arguments].
    /// The rest of the binders are appended to the `scope`.
    ///
    /// Note that the returned expression will have escaping variables and it is up to the caller to
    /// put it under an appropriate number of binders.
    ///
    /// Prefer using [`InferCtxt::fresh_kvar`] when possible.
    ///
    /// [binders]: rty::Binder
    /// [kvar]: rty::KVar
    /// [`InferCtxt::fresh_kvar`]: crate::infer::InferCtxt::fresh_kvar
    /// [self arguments]: rty::KVar::self_args
    /// [`BoundVariableKind::Refine`]: rty::BoundVariableKind::Refine
    pub fn fresh(
        &mut self,
        binders: &[rty::BoundVariableKinds],
        scope: impl IntoIterator<Item = (rty::Var, rty::Sort)>,
        encoding: KVarEncoding,
    ) -> rty::Expr {
        if self.dummy {
            return rty::Expr::hole(rty::HoleKind::Pred);
        }

        let args = itertools::chain(
            binders.iter().rev().enumerate().flat_map(|(level, vars)| {
                let debruijn = DebruijnIndex::from_usize(level);
                vars.iter()
                    .cloned()
                    .enumerate()
                    .flat_map(move |(idx, var)| {
                        if let rty::BoundVariableKind::Refine(sort, _, kind) = var {
                            let br = rty::BoundReft { var: BoundVar::from_usize(idx), kind };
                            Some((rty::Var::Bound(debruijn, br), sort))
                        } else {
                            None
                        }
                    })
            }),
            scope,
        );
        let [.., last] = binders else {
            return self.fresh_inner(0, [], encoding);
        };
        let num_self_args = last
            .iter()
            .filter(|var| matches!(var, rty::BoundVariableKind::Refine(..)))
            .count();
        self.fresh_inner(num_self_args, args, encoding)
    }

    fn fresh_inner<A>(&mut self, self_args: usize, args: A, encoding: KVarEncoding) -> rty::Expr
    where
        A: IntoIterator<Item = (rty::Var, rty::Sort)>,
    {
        // asset last one has things
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

#[derive(Default)]
struct ConstEnv<'tcx> {
    const_map: ConstMap<'tcx>,
    const_map_rev: HashMap<fixpoint::GlobalVar, ConstKey<'tcx>>,
    global_var_gen: IndexGen<fixpoint::GlobalVar>,
    fun_def_map: FunDefMap,
}

impl<'tcx> ConstEnv<'tcx> {
    fn get_or_insert(
        &mut self,
        key: ConstKey<'tcx>,
        // make_name: impl FnOnce() -> fixpoint::GlobalVar,
        make_const_decl: impl FnOnce(fixpoint::GlobalVar) -> fixpoint::ConstDecl,
    ) -> &fixpoint::ConstDecl {
        self.const_map.entry(key.clone()).or_insert_with(|| {
            let global_name = self.global_var_gen.fresh();
            self.const_map_rev.insert(global_name, key);
            make_const_decl(global_name)
        })
    }
}

struct ExprEncodingCtxt<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    local_var_env: LocalVarEnv,
    const_env: ConstEnv<'tcx>,
    errors: Errors<'genv>,
    /// Id of the item being checked. This is a [`MaybeExternId`] because we may be encoding
    /// invariants for an extern spec on an enum.
    def_id: MaybeExternId,
    infcx: rustc_infer::infer::InferCtxt<'tcx>,
}

impl<'genv, 'tcx> ExprEncodingCtxt<'genv, 'tcx> {
    fn new(genv: GlobalEnv<'genv, 'tcx>, def_id: MaybeExternId) -> Self {
        Self {
            genv,
            local_var_env: LocalVarEnv::new(),
            const_env: Default::default(),
            errors: Errors::new(genv.sess()),
            def_id,
            infcx: genv
                .tcx()
                .infer_ctxt()
                .with_next_trait_solver(true)
                .build(TypingMode::non_body_analysis()),
        }
    }

    fn def_span(&self) -> Span {
        self.genv.tcx().def_span(self.def_id)
    }

    fn var_to_fixpoint(&self, var: &rty::Var) -> fixpoint::Var {
        match var {
            rty::Var::Free(name) => {
                self.local_var_env
                    .get_fvar(*name)
                    .unwrap_or_else(|| {
                        span_bug!(self.def_span(), "no entry found for name: `{name:?}`")
                    })
                    .into()
            }
            rty::Var::Bound(debruijn, breft) => {
                self.local_var_env
                    .get_late_bvar(*debruijn, breft.var)
                    .unwrap_or_else(|| {
                        span_bug!(self.def_span(), "no entry found for late bound var: `{breft:?}`")
                    })
                    .into()
            }
            rty::Var::ConstGeneric(param) => fixpoint::Var::ConstGeneric(*param),
            rty::Var::EarlyParam(param) => fixpoint::Var::Param(*param),
            rty::Var::EVar(_) => {
                span_bug!(self.def_span(), "unexpected evar: `{var:?}`")
            }
        }
    }

    fn variant_to_fixpoint(
        &self,
        scx: &mut SortEncodingCtxt,
        enum_def_id: &DefId,
        idx: VariantIdx,
    ) -> fixpoint::Var {
        let adt_id = scx.declare_adt(*enum_def_id);
        fixpoint::Var::DataCtor(adt_id, idx)
    }

    fn struct_fields_to_fixpoint(
        &mut self,
        did: &DefId,
        flds: &[rty::Expr],
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        // do not generate 1-tuples
        if let [fld] = flds {
            self.expr_to_fixpoint(fld, scx)
        } else {
            let adt_id = scx.declare_adt(*did);
            let ctor = fixpoint::Expr::Var(fixpoint::Var::DataCtor(adt_id, VariantIdx::ZERO));
            let args = flds
                .iter()
                .map(|fld| self.expr_to_fixpoint(fld, scx))
                .try_collect()?;
            Ok(fixpoint::Expr::App(Box::new(ctor), args))
        }
    }

    fn fields_to_fixpoint(
        &mut self,
        flds: &[rty::Expr],
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        // do not generate 1-tuples
        if let [fld] = flds {
            self.expr_to_fixpoint(fld, scx)
        } else {
            scx.declare_tuple(flds.len());
            let ctor = fixpoint::Expr::Var(fixpoint::Var::TupleCtor { arity: flds.len() });
            let args = flds
                .iter()
                .map(|fld| self.expr_to_fixpoint(fld, scx))
                .try_collect()?;
            Ok(fixpoint::Expr::App(Box::new(ctor), args))
        }
    }

    fn internal_func_to_fixpoint(
        &mut self,
        internal_func: &InternalFuncKind,
        sort_args: &[rty::SortArg],
        args: &[rty::Expr],
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        match internal_func {
            InternalFuncKind::Val(op) => {
                let func = fixpoint::Expr::Var(self.define_const_for_prim_op(op, scx));
                let args = self.exprs_to_fixpoint(args, scx)?;
                Ok(fixpoint::Expr::App(Box::new(func), args))
            }
            InternalFuncKind::Rel(op) => {
                let expr = if let Some(prim_rel) = self.genv.prim_rel_for(op)? {
                    prim_rel.body.replace_bound_refts(args)
                } else {
                    rty::Expr::tt()
                };
                self.expr_to_fixpoint(&expr, scx)
            }
            InternalFuncKind::Cast => {
                let [rty::SortArg::Sort(from), rty::SortArg::Sort(to)] = &sort_args else {
                    span_bug!(self.def_span(), "unexpected cast")
                };
                match from.cast_kind(to) {
                    rty::CastKind::Identity => self.expr_to_fixpoint(&args[0], scx),
                    rty::CastKind::BoolToInt => {
                        Ok(fixpoint::Expr::IfThenElse(Box::new([
                            self.expr_to_fixpoint(&args[0], scx)?,
                            fixpoint::Expr::int(1),
                            fixpoint::Expr::int(0),
                        ])))
                    }
                    rty::CastKind::IntoUnit => self.expr_to_fixpoint(&rty::Expr::unit(), scx),
                    rty::CastKind::Uninterpreted => {
                        let func = fixpoint::Expr::Var(self.define_const_for_cast(from, to, scx));
                        let args = self.exprs_to_fixpoint(args, scx)?;
                        Ok(fixpoint::Expr::App(Box::new(func), args))
                    }
                }
            }
        }
    }

    fn structurally_normalize_expr(&self, expr: &rty::Expr) -> QueryResult<rty::Expr> {
        structurally_normalize_expr(self.genv, self.def_id.resolved_id(), &self.infcx, expr)
    }

    fn expr_to_fixpoint(
        &mut self,
        expr: &rty::Expr,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        let expr = self.structurally_normalize_expr(expr)?;
        let e = match expr.kind() {
            rty::ExprKind::Var(var) => fixpoint::Expr::Var(self.var_to_fixpoint(var)),
            rty::ExprKind::Constant(c) => const_to_fixpoint(*c),
            rty::ExprKind::BinaryOp(op, e1, e2) => self.bin_op_to_fixpoint(op, e1, e2, scx)?,
            rty::ExprKind::UnaryOp(op, e) => self.un_op_to_fixpoint(*op, e, scx)?,
            rty::ExprKind::FieldProj(e, proj) => self.proj_to_fixpoint(e, *proj, scx)?,
            rty::ExprKind::Tuple(flds) => self.fields_to_fixpoint(flds, scx)?,
            rty::ExprKind::Ctor(rty::Ctor::Struct(did), flds) => {
                self.struct_fields_to_fixpoint(did, flds, scx)?
            }
            rty::ExprKind::IsCtor(def_id, variant_idx, e) => {
                let ctor = self.variant_to_fixpoint(scx, def_id, *variant_idx);
                let e = self.expr_to_fixpoint(e, scx)?;
                fixpoint::Expr::IsCtor(ctor, Box::new(e))
            }
            rty::ExprKind::Ctor(rty::Ctor::Enum(did, idx), args) => {
                let ctor = self.variant_to_fixpoint(scx, did, *idx);
                let args = self.exprs_to_fixpoint(args, scx)?;
                fixpoint::Expr::App(Box::new(fixpoint::Expr::Var(ctor)), args)
            }
            rty::ExprKind::ConstDefId(did) => {
                let var = self.define_const_for_rust_const(*did, scx);
                fixpoint::Expr::Var(var)
            }
            rty::ExprKind::App(func, sort_args, args) => {
                if let rty::ExprKind::InternalFunc(func) = func.kind() {
                    self.internal_func_to_fixpoint(func, sort_args, args, scx)?
                } else {
                    let func = self.expr_to_fixpoint(func, scx)?;
                    let args = self.exprs_to_fixpoint(args, scx)?;
                    fixpoint::Expr::App(Box::new(func), args)
                }
            }
            rty::ExprKind::IfThenElse(p, e1, e2) => {
                fixpoint::Expr::IfThenElse(Box::new([
                    self.expr_to_fixpoint(p, scx)?,
                    self.expr_to_fixpoint(e1, scx)?,
                    self.expr_to_fixpoint(e2, scx)?,
                ]))
            }
            rty::ExprKind::Alias(alias_reft, args) => {
                let sort = self.genv.sort_of_assoc_reft(alias_reft.assoc_id)?;
                let sort = sort.instantiate_identity();
                let func =
                    fixpoint::Expr::Var(self.define_const_for_alias_reft(alias_reft, sort, scx));
                let args = args
                    .iter()
                    .map(|expr| self.expr_to_fixpoint(expr, scx))
                    .try_collect()?;
                fixpoint::Expr::App(Box::new(func), args)
            }
            rty::ExprKind::Abs(lam) => {
                let var = self.define_const_for_lambda(lam, scx);
                fixpoint::Expr::Var(var)
            }
            rty::ExprKind::Let(init, body) => {
                debug_assert_eq!(body.vars().len(), 1);
                let init = self.expr_to_fixpoint(init, scx)?;

                self.local_var_env.push_layer_with_fresh_names(1);
                let body = self.expr_to_fixpoint(body.skip_binder_ref(), scx)?;
                let vars = self.local_var_env.pop_layer();

                fixpoint::Expr::Let(vars[0].into(), Box::new([init, body]))
            }
            rty::ExprKind::GlobalFunc(SpecFuncKind::Thy(itf)) => fixpoint::Expr::ThyFunc(*itf),
            rty::ExprKind::GlobalFunc(SpecFuncKind::Uif(def_id)) => {
                fixpoint::Expr::Var(self.define_const_for_uif(*def_id, scx))
            }
            rty::ExprKind::GlobalFunc(SpecFuncKind::Def(def_id)) => {
                fixpoint::Expr::Var(self.declare_fun(*def_id))
            }
            rty::ExprKind::Hole(..)
            | rty::ExprKind::KVar(_)
            | rty::ExprKind::Local(_)
            | rty::ExprKind::PathProj(..)
            | rty::ExprKind::ForAll(_)
            | rty::ExprKind::InternalFunc(_) => {
                span_bug!(self.def_span(), "unexpected expr: `{expr:?}`")
            }
            rty::ExprKind::BoundedQuant(kind, rng, body) => {
                let exprs = (rng.start..rng.end).map(|i| {
                    let arg = rty::Expr::constant(rty::Constant::from(i));
                    body.replace_bound_reft(&arg)
                });
                let expr = match kind {
                    flux_middle::fhir::QuantKind::Forall => rty::Expr::and_from_iter(exprs),
                    flux_middle::fhir::QuantKind::Exists => rty::Expr::or_from_iter(exprs),
                };
                self.expr_to_fixpoint(&expr, scx)?
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

    fn proj_to_fixpoint(
        &mut self,
        e: &rty::Expr,
        proj: rty::FieldProj,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        let arity = proj.arity(self.genv)?;
        // we encode 1-tuples as the single element inside so no projection necessary here
        if arity == 1 {
            self.expr_to_fixpoint(e, scx)
        } else {
            let proj = match proj {
                rty::FieldProj::Tuple { arity, field } => {
                    scx.declare_tuple(arity);
                    fixpoint::Var::TupleProj { arity, field }
                }
                rty::FieldProj::Adt { def_id, field } => {
                    let adt_id = scx.declare_adt(def_id);
                    fixpoint::Var::DataProj { adt_id, field }
                }
            };
            let proj = fixpoint::Expr::Var(proj);
            Ok(fixpoint::Expr::App(Box::new(proj), vec![self.expr_to_fixpoint(e, scx)?]))
        }
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

    fn bv_rel_to_fixpoint(&self, rel: &fixpoint::BinRel) -> fixpoint::Expr {
        let itf = match rel {
            fixpoint::BinRel::Gt => fixpoint::ThyFunc::BvUgt,
            fixpoint::BinRel::Ge => fixpoint::ThyFunc::BvUge,
            fixpoint::BinRel::Lt => fixpoint::ThyFunc::BvUlt,
            fixpoint::BinRel::Le => fixpoint::ThyFunc::BvUle,
            _ => span_bug!(self.def_span(), "not a bitvector relation!"),
        };
        fixpoint::Expr::ThyFunc(itf)
    }

    fn bv_op_to_fixpoint(&self, op: &rty::BinOp) -> fixpoint::Expr {
        let itf = match op {
            rty::BinOp::Add(_) => fixpoint::ThyFunc::BvAdd,
            rty::BinOp::Sub(_) => fixpoint::ThyFunc::BvSub,
            rty::BinOp::Mul(_) => fixpoint::ThyFunc::BvMul,
            rty::BinOp::Div(_) => fixpoint::ThyFunc::BvUdiv,
            rty::BinOp::Mod(_) => fixpoint::ThyFunc::BvUrem,
            rty::BinOp::BitAnd => fixpoint::ThyFunc::BvAnd,
            rty::BinOp::BitOr => fixpoint::ThyFunc::BvOr,
            rty::BinOp::BitXor => fixpoint::ThyFunc::BvXor,
            rty::BinOp::BitShl => fixpoint::ThyFunc::BvShl,
            rty::BinOp::BitShr => fixpoint::ThyFunc::BvLshr,
            _ => span_bug!(self.def_span(), "not a bitvector operation!"),
        };
        fixpoint::Expr::ThyFunc(itf)
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
                ));
            }
            rty::BinOp::Ne => {
                return Ok(fixpoint::Expr::Atom(
                    fixpoint::BinRel::Ne,
                    Box::new([self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?]),
                ));
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
                ]));
            }
            rty::BinOp::Or => {
                return Ok(fixpoint::Expr::Or(vec![
                    self.expr_to_fixpoint(e1, scx)?,
                    self.expr_to_fixpoint(e2, scx)?,
                ]));
            }
            rty::BinOp::Imp => {
                return Ok(fixpoint::Expr::Imp(Box::new([
                    self.expr_to_fixpoint(e1, scx)?,
                    self.expr_to_fixpoint(e2, scx)?,
                ])));
            }
            rty::BinOp::Iff => {
                return Ok(fixpoint::Expr::Iff(Box::new([
                    self.expr_to_fixpoint(e1, scx)?,
                    self.expr_to_fixpoint(e2, scx)?,
                ])));
            }
            rty::BinOp::Add(rty::Sort::BitVec(_))
            | rty::BinOp::Sub(rty::Sort::BitVec(_))
            | rty::BinOp::Mul(rty::Sort::BitVec(_))
            | rty::BinOp::Div(rty::Sort::BitVec(_))
            | rty::BinOp::Mod(rty::Sort::BitVec(_))
            | rty::BinOp::BitAnd
            | rty::BinOp::BitOr
            | rty::BinOp::BitXor
            | rty::BinOp::BitShl
            | rty::BinOp::BitShr => {
                let bv_func = self.bv_op_to_fixpoint(op);
                return Ok(fixpoint::Expr::App(
                    Box::new(bv_func),
                    vec![self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?],
                ));
            }
            rty::BinOp::Add(_) => fixpoint::BinOp::Add,
            rty::BinOp::Sub(_) => fixpoint::BinOp::Sub,
            rty::BinOp::Mul(_) => fixpoint::BinOp::Mul,
            rty::BinOp::Div(_) => fixpoint::BinOp::Div,
            rty::BinOp::Mod(_) => fixpoint::BinOp::Mod,
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
    /// [the encoding]: Self::define_const_for_lambda
    fn bin_rel_to_fixpoint(
        &mut self,
        sort: &rty::Sort,
        rel: fixpoint::BinRel,
        e1: &rty::Expr,
        e2: &rty::Expr,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        let e = match sort {
            rty::Sort::Int | rty::Sort::Real | rty::Sort::Char => {
                fixpoint::Expr::Atom(
                    rel,
                    Box::new([self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?]),
                )
            }
            rty::Sort::BitVec(_) => {
                let e1 = self.expr_to_fixpoint(e1, scx)?;
                let e2 = self.expr_to_fixpoint(e2, scx)?;
                let rel = self.bv_rel_to_fixpoint(&rel);
                fixpoint::Expr::App(Box::new(rel), vec![e1, e2])
            }
            rty::Sort::Tuple(sorts) => {
                let arity = sorts.len();
                self.apply_bin_rel_rec(sorts, rel, e1, e2, scx, |field| {
                    rty::FieldProj::Tuple { arity, field }
                })?
            }
            rty::Sort::App(rty::SortCtor::Adt(sort_def), args)
                if let Some(variant) = sort_def.opt_struct_variant() =>
            {
                let def_id = sort_def.did();
                let sorts = variant.field_sorts(args);
                self.apply_bin_rel_rec(&sorts, rel, e1, e2, scx, |field| {
                    rty::FieldProj::Adt { def_id, field }
                })?
            }
            _ => {
                let rel = fixpoint::Expr::Var(fixpoint::Var::UIFRel(rel));
                fixpoint::Expr::App(
                    Box::new(rel),
                    vec![self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?],
                )
            }
        };
        Ok(e)
    }

    /// Apply binary relation recursively over aggregate expressions
    fn apply_bin_rel_rec(
        &mut self,
        sorts: &[rty::Sort],
        rel: fixpoint::BinRel,
        e1: &rty::Expr,
        e2: &rty::Expr,
        scx: &mut SortEncodingCtxt,
        mk_proj: impl Fn(u32) -> rty::FieldProj,
    ) -> QueryResult<fixpoint::Expr> {
        Ok(fixpoint::Expr::and(
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

    fn imm(
        &mut self,
        arg: &rty::Expr,
        sort: &rty::Sort,
        scx: &mut SortEncodingCtxt,
        bindings: &mut Vec<fixpoint::Bind>,
    ) -> QueryResult<fixpoint::Var> {
        let arg = self.expr_to_fixpoint(arg, scx)?;
        // Check if it's a variable after encoding, in case the encoding produced a variable from a
        // non-variable.
        if let fixpoint::Expr::Var(var) = arg {
            Ok(var)
        } else {
            let fresh = self.local_var_env.fresh_name();
            let pred = fixpoint::Expr::eq(fixpoint::Expr::Var(fresh.into()), arg);
            bindings.push(fixpoint::Bind {
                name: fresh.into(),
                sort: scx.sort_to_fixpoint(sort),
                pred: fixpoint::Pred::Expr(pred),
            });
            Ok(fresh.into())
        }
    }

    /// Declare that the `def_id` of a Flux function definition needs to be encoded and assigns
    /// a name to it if it hasn't yet been declared. The encoding of the function body happens
    /// in [`Self::define_funs`].
    fn declare_fun(&mut self, def_id: FluxDefId) -> fixpoint::Var {
        *self.const_env.fun_def_map.entry(def_id).or_insert_with(|| {
            let id = self.const_env.global_var_gen.fresh();
            fixpoint::Var::Global(id, Some(def_id.name()))
        })
    }

    /// The logic below is a bit "duplicated" with the `[`prim_op_sort`] in sortck.rs;
    /// They are not exactly the same because this is on rty and the other one on fhir.
    /// We should make sure these two remain in sync.
    ///
    /// (NOTE:PrimOpSort) We are somewhat "overloading" the BinOps: as we are using them
    /// for (a) interpreted operations on bit vectors AND (b) uninterpreted functions on integers.
    /// So when Binop::BitShr (a) appears in a ExprKind::BinOp, it means bit vectors, but
    /// (b) inside ExprKind::InternalFunc it means int.
    fn prim_op_sort(op: &rty::BinOp, span: Span) -> rty::PolyFuncSort {
        match op {
            rty::BinOp::BitAnd
            | rty::BinOp::BitOr
            | rty::BinOp::BitXor
            | rty::BinOp::BitShl
            | rty::BinOp::BitShr => {
                let fsort =
                    rty::FuncSort::new(vec![rty::Sort::Int, rty::Sort::Int], rty::Sort::Int);
                rty::PolyFuncSort::new(List::empty(), fsort)
            }
            _ => span_bug!(span, "unexpected prim op: {op:?} in `prim_op_sort`"),
        }
    }

    fn define_const_for_cast(
        &mut self,
        from: &rty::Sort,
        to: &rty::Sort,
        scx: &mut SortEncodingCtxt,
    ) -> fixpoint::Var {
        let key = ConstKey::Cast(from.clone(), to.clone());
        self.const_env
            .get_or_insert(key, |global_name| {
                let fsort = rty::FuncSort::new(vec![from.clone()], to.clone());
                let fsort = rty::PolyFuncSort::new(List::empty(), fsort);
                let sort = scx.func_sort_to_fixpoint(&fsort);
                fixpoint::ConstDecl {
                    name: fixpoint::Var::Global(global_name, None),
                    sort,
                    comment: Some(format!("cast uif: ({from:?}) -> {to:?}")),
                }
            })
            .name
    }

    fn define_const_for_prim_op(
        &mut self,
        op: &rty::BinOp,
        scx: &mut SortEncodingCtxt,
    ) -> fixpoint::Var {
        let key = ConstKey::PrimOp(op.clone());
        let span = self.def_span();
        self.const_env
            .get_or_insert(key, |global_name| {
                let sort = scx.func_sort_to_fixpoint(&Self::prim_op_sort(op, span));
                fixpoint::ConstDecl {
                    name: fixpoint::Var::Global(global_name, None),
                    sort,
                    comment: Some(format!("prim op uif: {op:?}")),
                }
            })
            .name
    }

    fn define_const_for_uif(
        &mut self,
        def_id: FluxDefId,
        scx: &mut SortEncodingCtxt,
    ) -> fixpoint::Var {
        let key = ConstKey::Uif(def_id);
        self.const_env
            .get_or_insert(key, |global_name| {
                let sort = scx.func_sort_to_fixpoint(&self.genv.func_sort(def_id));
                fixpoint::ConstDecl {
                    name: fixpoint::Var::Global(global_name, Some(def_id.name())),
                    sort,
                    comment: Some(format!("uif: {def_id:?}")),
                }
            })
            .name
    }

    fn define_const_for_rust_const(
        &mut self,
        def_id: DefId,
        scx: &mut SortEncodingCtxt,
    ) -> fixpoint::Var {
        let key = ConstKey::RustConst(def_id);
        self.const_env
            .get_or_insert(key, |global_name| {
                let sort = self.genv.sort_of_def_id(def_id).unwrap().unwrap();
                fixpoint::ConstDecl {
                    name: fixpoint::Var::Global(global_name, None),
                    sort: scx.sort_to_fixpoint(&sort),
                    comment: Some(format!("rust const: {}", def_id_to_string(def_id))),
                }
            })
            .name
    }

    /// returns the 'constant' UIF for Var used to represent the alias_pred, creating and adding it
    /// to the const_map if necessary
    fn define_const_for_alias_reft(
        &mut self,
        alias_reft: &rty::AliasReft,
        fsort: rty::FuncSort,
        scx: &mut SortEncodingCtxt,
    ) -> fixpoint::Var {
        let tcx = self.genv.tcx();
        let args = alias_reft
            .args
            .to_rustc(tcx)
            .truncate_to(tcx, tcx.generics_of(alias_reft.assoc_id.parent()));
        let key = ConstKey::Alias(alias_reft.assoc_id, args);
        self.const_env
            .get_or_insert(key, |global_name| {
                let comment = Some(format!("alias reft: {alias_reft:?}"));
                let name = fixpoint::Var::Global(global_name, None);
                let fsort = rty::PolyFuncSort::new(List::empty(), fsort);
                let sort = scx.func_sort_to_fixpoint(&fsort);
                fixpoint::ConstDecl { name, comment, sort }
            })
            .name
    }

    /// We encode lambdas with uninterpreted constant. Two syntactically equal lambdas will be encoded
    /// with the same constant.
    fn define_const_for_lambda(
        &mut self,
        lam: &rty::Lambda,
        scx: &mut SortEncodingCtxt,
    ) -> fixpoint::Var {
        let key = ConstKey::Lambda(lam.clone());
        self.const_env
            .get_or_insert(key, |global_name| {
                let comment = Some(format!("lambda: {lam:?}"));
                let name = fixpoint::Var::Global(global_name, None);
                let sort = scx.func_sort_to_fixpoint(&lam.fsort().to_poly());
                fixpoint::ConstDecl { name, comment, sort }
            })
            .name
    }

    fn assume_const_values(
        &mut self,
        mut constraint: fixpoint::Constraint,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Constraint> {
        // Encoding the value for a constant could in theory define more constants for which
        // we need to assume values, so we iterate until there are no more constants.
        let mut idx = 0;
        while let Some((key, const_)) = self.const_env.const_map.get_index(idx) {
            idx += 1;

            let ConstKey::RustConst(def_id) = key else { continue };
            let info = self.genv.constant_info(def_id)?;
            match info {
                rty::ConstantInfo::Uninterpreted => {}
                rty::ConstantInfo::Interpreted(val, _) => {
                    let e1 = fixpoint::Expr::Var(const_.name);
                    let e2 = self.expr_to_fixpoint(&val, scx)?;
                    let pred = fixpoint::Pred::Expr(e1.eq(e2));
                    constraint = fixpoint::Constraint::ForAll(
                        fixpoint::Bind {
                            name: fixpoint::Var::Underscore,
                            sort: fixpoint::Sort::Int,
                            pred,
                        },
                        Box::new(constraint),
                    );
                }
            }
        }
        Ok(constraint)
    }

    fn qualifiers_for(
        &mut self,
        def_id: LocalDefId,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<Vec<fixpoint::Qualifier>> {
        self.genv
            .qualifiers_for(def_id)?
            .map(|qual| self.qualifier_to_fixpoint(qual, scx))
            .try_collect()
    }

    fn define_funs(
        &mut self,
        def_id: MaybeExternId,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<(Vec<fixpoint::FunDef>, Vec<fixpoint::ConstDecl>)> {
        let reveals: UnordSet<FluxDefId> = self
            .genv
            .reveals_for(def_id.local_id())
            .iter()
            .copied()
            .collect();
        let proven_externally = self.genv.proven_externally(def_id.local_id());
        let mut consts = vec![];
        let mut defs = vec![];

        // We iterate until encoding the body of functions doesn't require any more functions
        // to be encoded.
        let mut idx = 0;
        while let Some((&did, &name)) = self.const_env.fun_def_map.get_index(idx) {
            idx += 1;

            let comment = format!("flux def: {did:?}");
            let info = self.genv.normalized_info(did);
            let revealed = reveals.contains(&did);
            if info.hide && !revealed && !proven_externally {
                let sort = scx.func_sort_to_fixpoint(&self.genv.func_sort(did));
                consts.push(fixpoint::ConstDecl { name, sort, comment: Some(comment) });
            } else {
                let out = scx.sort_to_fixpoint(self.genv.func_sort(did).expect_mono().output());
                let (args, body) = self.body_to_fixpoint(&info.body, scx)?;
                let fun_def = fixpoint::FunDef { name, args, body, out, comment: Some(comment) };
                defs.push((info.rank, fun_def));
            };
        }

        // we sort by rank so the definitions go out without any forward dependencies.
        let defs = defs
            .into_iter()
            .sorted_by_key(|(rank, _)| *rank)
            .map(|(_, def)| def)
            .collect();

        Ok((defs, consts))
    }

    fn body_to_fixpoint(
        &mut self,
        body: &rty::Binder<rty::Expr>,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<(Vec<(fixpoint::Var, fixpoint::Sort)>, fixpoint::Expr)> {
        self.local_var_env
            .push_layer_with_fresh_names(body.vars().len());

        let expr = self.expr_to_fixpoint(body.as_ref().skip_binder(), scx)?;

        let args: Vec<(fixpoint::Var, fixpoint::Sort)> =
            iter::zip(self.local_var_env.pop_layer(), body.vars())
                .map(|(name, var)| (name.into(), scx.sort_to_fixpoint(var.expect_sort())))
                .collect();

        Ok((args, expr))
    }

    fn qualifier_to_fixpoint(
        &mut self,
        qualifier: &rty::Qualifier,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Qualifier> {
        let (args, body) = self.body_to_fixpoint(&qualifier.body, scx)?;
        let name = qualifier.def_id.name().to_string();
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
