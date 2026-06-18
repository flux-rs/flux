//! Encoding of the refinement tree into a fixpoint constraint.

#[cfg(feature = "wick")]
use std::collections::HashSet;
use std::{collections::HashMap, hash::Hash, iter, ops::Range};

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
use flux_macros::DebugAsJson;
use flux_middle::{
    FixpointQueryKind,
    def_id::{FluxDefId, MaybeExternId},
    def_id_to_string,
    global_env::GlobalEnv,
    metrics::{self, Metric, TimingKind, time_it},
    pretty::{NestedString, PrettyCx, PrettyNested},
    queries::QueryResult,
    query_bug,
    rty::{
        self, ESpan, EarlyReftParam, GenericArgsExt, InternalFuncKind, Lambda, List, SpecFuncKind,
        VariantIdx,
        fold::{TypeFoldable as _, TypeVisitable},
    },
};
use itertools::Itertools;
use liquid_fixpoint::{
    FixpointResult, FixpointStatus, SmtSolver,
    parser::{FromSexp, ParseError},
    sexp::Parser,
};
#[cfg(feature = "wick")]
use liquid_fixpoint::{check_validity, qe_and_simplify};
use rustc_data_structures::{
    fx::{FxHashMap, FxIndexMap, FxIndexSet},
    unord::{UnordMap, UnordSet},
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::newtype_index;
use rustc_infer::infer::TyCtxtInferExt as _;
use rustc_middle::ty::TypingMode;
use rustc_span::{DUMMY_SP, Span, Symbol};
use rustc_type_ir::{BoundVar, DebruijnIndex};
use serde::{Deserialize, Deserializer, Serialize};

#[cfg(feature = "wick")]
use crate::wkvars::WKVarInstantiator;
use crate::{
    fixpoint_encoding::fixpoint::FixpointTypes, fixpoint_qualifiers::FIXPOINT_QUALIFIERS,
    lean_encoding::LeanEncoder, projections::structurally_normalize_expr,
};

pub mod decoding;
use crate::refine_tree::BlameAnalysis;

pub mod fixpoint {
    use std::fmt;

    use flux_middle::{self, def_id::FluxDefId, rty::EarlyReftParam};
    use liquid_fixpoint::{FixpointFmt, Identifier};
    use rustc_abi::VariantIdx;
    use rustc_index::newtype_index;
    use rustc_middle::ty::ParamConst;
    use rustc_span::Symbol;

    newtype_index! {
        #[orderable]
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
        /// Unique id assigned to each [`rty::AdtSortDef`] that needs to be encoded
        /// into fixpoint
        pub struct AdtId {}
    }

    #[derive(Hash, Copy, Clone, Debug, PartialEq, Eq)]
    pub enum Var {
        Underscore,
        Global(GlobalVar, Option<Symbol>),
        WKVar(Symbol, u32),
        UnderscoreInvariant,
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
                Var::Global(v, Some(name)) => write!(f, "f${}${}", name, v.as_u32()),
                Var::WKVar(def, idx) => write!(f, "wk${}${}", def, idx),
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
                Var::UnderscoreInvariant => write!(f, "_invariant$"), // Not sure what kind of names can appear, but probably doesn't hurt to put a $ for uniqueness
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
        User(FluxDefId),
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
                // There's no way to declare opaque sorts in the fixpoint horn syntax so we encode user
                // declared opaque sorts as integers. Well-formedness should ensure values of these
                // sorts are used "opaquely", i.e., the only values of these sorts are variables.
                DataSort::User(..) => {
                    write!(f, "int")
                }
            }
        }
    }

    #[derive(Hash, Clone, Debug, PartialEq, Eq)]
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

/// A type to represent Solutions for KVars
pub type Solution = HashMap<rty::KVid, rty::Binder<rty::Expr>>;
pub type FixpointSolution = HashMap<fixpoint::KVid, (Vec<fixpoint::Sort>, fixpoint::Expr)>;

/// A very explicit representation of [`Solution`] for debugging/tracing/serialization ONLY.
#[derive(Serialize, DebugAsJson)]
pub struct SolutionTrace(Vec<KvarSolutionTrace>);

#[derive(Serialize, DebugAsJson)]
pub struct KvarSolutionTrace {
    pub name: String,
    pub args: Vec<String>,
    pub body: NestedString,
}

impl KvarSolutionTrace {
    pub fn new(cx: &PrettyCx, kvid: rty::KVid, bind_expr: &rty::Binder<rty::Expr>) -> Self {
        let mut args = Vec::new();
        let body = cx
            .nested_with_bound_vars("", bind_expr.vars(), Some("".to_string()), |prefix| {
                for arg in prefix.split(',').map(|s| s.trim().to_string()) {
                    args.push(arg);
                }
                bind_expr.skip_binder_ref().fmt_nested(cx)
            })
            .unwrap();

        KvarSolutionTrace { name: format!("{kvid:?}"), args, body }
    }
}

impl SolutionTrace {
    pub fn new(genv: GlobalEnv, solution: &Solution) -> Self {
        let cx = &PrettyCx::default(genv);
        let res = solution
            .iter()
            .map(|(kvid, bind_expr)| KvarSolutionTrace::new(cx, *kvid, bind_expr))
            .collect();
        SolutionTrace(res)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Answer<Tag> {
    pub errors: Vec<FixpointCheckError<Tag>>,
    pub solution: Solution,
}

impl<Tag> Answer<Tag> {
    pub fn trivial() -> Self {
        Self { errors: Vec::new(), solution: HashMap::new() }
    }
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
pub struct SortEncodingCtxt {
    /// Set of all the tuple arities that need to be defined
    tuples: UnordSet<usize>,
    /// Set of all the [`AdtDefSortDef`](rty::AdtSortDef) that need to be declared as
    /// Fixpoint data-decls
    adt_sorts: FxIndexSet<DefId>,
    /// Set of all opaque types that need to be defined
    user_sorts: FxIndexSet<FluxDefId>,
}

impl SortEncodingCtxt {
    pub fn sort_to_fixpoint(&mut self, sort: &rty::Sort) -> fixpoint::Sort {
        match sort {
            rty::Sort::Int => fixpoint::Sort::Int,
            rty::Sort::Real => fixpoint::Sort::Real,
            rty::Sort::Bool => fixpoint::Sort::Bool,
            rty::Sort::Str => fixpoint::Sort::Str,
            rty::Sort::Char => fixpoint::Sort::Int,
            rty::Sort::BitVec(size) => fixpoint::Sort::BitVec(Box::new(bv_size_to_fixpoint(*size))),
            rty::Sort::App(rty::SortCtor::User(def_id), args) => {
                self.declare_opaque_sort(*def_id);
                let args = args.iter().map(|s| self.sort_to_fixpoint(s)).collect_vec();
                fixpoint::Sort::App(
                    fixpoint::SortCtor::Data(fixpoint::DataSort::User(*def_id)),
                    args,
                )
            }
            // There's no way to declare opaque sorts in the fixpoint horn syntax so we encode type
            // parameter sorts and (unormalizable) type alias sorts as integers. Well-formedness
            // should ensure values of these sorts are used "opaquely", i.e., the only values of
            // these sorts are variables.
            rty::Sort::Param(_)
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
                if let Some(_variant) = sort_def.opt_struct_variant() {
                    // NOTE(ck): We previously had an optimization which didn't
                    // emit a Ctor in cases of a 1-tuple, but this makes the
                    // conversion back from fixpoint unfaithful (we can't
                    // distinguish between e.g. `usize` and `(usize,)`).
                    //
                    // So this optimization has since been removed. Arguably
                    // it's better-suited for fixpoint.
                    let adt_id = self.declare_adt(sort_def.did());
                    let ctor = fixpoint::SortCtor::Data(fixpoint::DataSort::Adt(adt_id));
                    let args = args.iter().map(|s| self.sort_to_fixpoint(s)).collect_vec();
                    fixpoint::Sort::App(ctor, args)
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
                // NOTE(cK): See above note about not generating 1-tuples.
                self.declare_tuple(sorts.len());
                let ctor = fixpoint::SortCtor::Data(fixpoint::DataSort::Tuple(sorts.len()));
                let args = sorts.iter().map(|s| self.sort_to_fixpoint(s)).collect();
                fixpoint::Sort::App(ctor, args)
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

    pub fn declare_opaque_sort(&mut self, def_id: FluxDefId) {
        self.user_sorts.insert(def_id);
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

    pub fn user_sorts_to_fixpoint(&mut self, genv: GlobalEnv) -> Vec<fixpoint::SortDecl> {
        self.user_sorts
            .iter()
            .map(|sort| {
                let param_count = genv.sort_decl_param_count(sort);
                fixpoint::SortDecl { name: fixpoint::DataSort::User(*sort), vars: param_count }
            })
            .collect()
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

    fn append_tuple_decls(tuples: &UnordSet<usize>, decls: &mut Vec<fixpoint::DataDecl>) {
        decls.extend(
            tuples
                .items()
                .into_sorted_stable_ord()
                .into_iter()
                .map(|arity| {
                    fixpoint::DataDecl {
                        name: fixpoint::DataSort::Tuple(*arity),
                        vars: *arity,
                        ctors: vec![fixpoint::DataCtor {
                            name: fixpoint::Var::TupleCtor { arity: *arity },
                            fields: (0..(*arity as u32))
                                .map(|field| {
                                    fixpoint::DataField {
                                        name: fixpoint::Var::TupleProj { arity: *arity, field },
                                        sort: fixpoint::Sort::Var(field as usize),
                                    }
                                })
                                .collect(),
                        }],
                    }
                }),
        );
    }

    pub fn encode_data_decls(&mut self, genv: GlobalEnv) -> QueryResult<Vec<fixpoint::DataDecl>> {
        let mut decls = vec![];
        self.append_adt_decls(genv, &mut decls)?;
        Self::append_tuple_decls(&self.tuples, &mut decls);
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

pub type FunDefMap = FxIndexMap<FluxDefId, fixpoint::Var>;
type ConstMap<'tcx> = FxIndexMap<ConstKey<'tcx>, fixpoint::ConstDecl>;

#[derive(Eq, Hash, PartialEq, Clone)]
enum ConstKey<'tcx> {
    Uif(FluxDefId),
    RustConst(DefId),
    Alias(FluxDefId, rustc_middle::ty::GenericArgsRef<'tcx>),
    Lambda(Lambda),
    PrimOp(rty::BinOp),
    Cast(rty::Sort, rty::Sort),
    WKVar(rty::WKVid, usize),
}

// #[derive(Debug, Clone)]
// pub struct BinderInfo {
//     pub name: Name,
//     pub provenance: Option<BinderProvenance>,
//     pub depth: usize,
// }

#[derive(Debug, Clone)]
pub struct BlameCtxt {
    pub blame_analysis: BlameAnalysis,
    pub expr: rty::Expr,
}

pub struct FixpointCtxt<'genv, 'tcx, T: Eq + Hash> {
    comments: Vec<String>,
    genv: GlobalEnv<'genv, 'tcx>,
    kvars: KVarGen,
    scx: SortEncodingCtxt,
    kcx: KVarEncodingCtxt,
    ecx: ExprEncodingCtxt<'genv, 'tcx>,
    tags: IndexVec<TagIdx, T>,
    _tags_inv: UnordMap<T, TagIdx>,
    pub blame_ctx_map: FxHashMap<TagIdx, BlameCtxt>,
}

pub type FixQueryCache = QueryCache<FixpointResult<TagIdx>>;

#[derive(Debug, Clone)]
pub struct FixpointCheckError<Tag> {
    pub tag: Tag,
    pub blame_ctx: BlameCtxt,
    pub possible_solutions: FxIndexMap<rty::WKVid, Vec<rty::Binder<rty::Expr>>>,
}

impl<Tag> FixpointCheckError<Tag> {
    pub fn new(
        tag: Tag,
        blame_ctx: BlameCtxt,
        possible_solutions: FxIndexMap<rty::WKVid, Vec<rty::Binder<rty::Expr>>>,
    ) -> Self {
        Self { tag, blame_ctx, possible_solutions }
    }
}

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
            ecx: ExprEncodingCtxt::new(genv, Some(def_id)),
            kcx: Default::default(),
            tags: IndexVec::new(),
            _tags_inv: Default::default(),
            blame_ctx_map: FxHashMap::default(),
        }
    }

    pub fn check(
        mut self,
        cache: &mut FixQueryCache,
        def_id: MaybeExternId,
        constraint: fixpoint::Constraint,
        kind: FixpointQueryKind,
        scrape_quals: bool,
        solver: SmtSolver,
        horn_backend: liquid_fixpoint::Backend,
    ) -> QueryResult<Answer<Tag>> {
        // skip checking trivial constraints
        let count = constraint.concrete_head_count();
        metrics::incr_metric(Metric::CsTotal, count as u32);
        if count == 0 {
            metrics::incr_metric_if(kind.is_body(), Metric::FnTrivial);
            self.ecx.errors.to_result()?;
            return Ok(Answer::trivial());
        }
        let def_span = self.ecx.def_span();
        let kvars = self.kcx.encode_kvars(&self.kvars, &mut self.scx);
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

        #[cfg(feature = "wick")]
        let mut flat_constraint_map: HashMap<TagIdx, fixpoint::FlatConstraint> = constraint
            .flatten(
                |var| matches!(var, fixpoint::Var::Underscore | fixpoint::Var::UnderscoreInvariant),
                |var| matches!(var, fixpoint::Var::UnderscoreInvariant),
            )
            .into_iter()
            .flat_map(|flat_constraint| {
                // We can't send a kvar to the SMT. If there's a kvar on the LHS we
                // can underapproximate it with TRUE, but if it's in head position
                // we don't know what to do.
                if let Some(tag) = flat_constraint.tag
                    && !flat_constraint.head.has_kvar()
                {
                    Some((tag.clone(), flat_constraint))
                } else {
                    None
                }
            })
            .collect();

        let mut constants = self.ecx.const_env.const_map.values().cloned().collect_vec();
        constants.extend(define_constants);

        // For hornspec, wkvars are declared via WKVarDecl (declare-fun), not as ConstDecl
        // (declare-const with a function sort). Strip them from constants to avoid double-declaration.
        if matches!(horn_backend, liquid_fixpoint::Backend::Hornspec) {
            constants.retain(|c| !matches!(c.name, fixpoint::Var::WKVar(..)));
        }

        #[cfg(feature = "wick")]
        let constants_without_inequalities = constants.clone();

        // The rust fixpoint implementation does not yet support polymorphic functions.
        // For now we avoid including these by default so that cases where they are not needed can work.
        // Should be removed when support is added.
        // Hornspec also doesn't support polymorphism, so skip for that backend too.
        #[cfg(not(feature = "rust-fixpoint"))]
        if matches!(horn_backend, liquid_fixpoint::Backend::Fixpoint) {
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
        }

        // We are done encoding expressions. Check if there are any errors.
        self.ecx.errors.to_result()?;

        let data_decls = self.scx.encode_data_decls(self.genv)?;

        let task = fixpoint::Task {
            comments: self.comments.clone(),
            constants,
            kvars,
            wkvars: self.ecx.wkvars.values().cloned().collect_vec(),
            define_funs,
            constraint,
            qualifiers,
            scrape_quals,
            solver,
            backend: horn_backend,
            data_decls: data_decls.clone(),
        };

        // For hornspec, flatten ADT/Tuple sorts into scalars so we don't emit
        // declare-datatypes (which hornspec doesn't support).
        let task = match horn_backend {
            liquid_fixpoint::Backend::Hornspec => adt_flatten::flatten_task(task),
            liquid_fixpoint::Backend::Fixpoint => task,
        };

        let id = def_id.resolved_id();
        if config::dump_constraint() {
            match horn_backend {
                liquid_fixpoint::Backend::Fixpoint => {
                    dbg::dump_item_info(self.genv.tcx(), id, "smt2", &task).unwrap();
                }
                liquid_fixpoint::Backend::Hornspec => {
                    dbg::dump_item_info(self.genv.tcx(), id, "horn", liquid_fixpoint::SmtFormatter(&task)).unwrap();
                }
            }
        }

        // Under the wick feature, build the hornspec task now (before the fixpoint run consumes
        // ownership of `task`) so we can run it later if fixpoint fails.
        #[cfg(feature = "wick")]
        let hornspec_task = {
            let mut t = task.clone();
            t.constants.retain(|c| {
                !matches!(c.name, fixpoint::Var::WKVar(..) | fixpoint::Var::UIFRel(..))
            });
            t.backend = liquid_fixpoint::Backend::Hornspec;
            adt_flatten::flatten_task(t)
        };

        let result = Self::run_task_with_cache(self.genv, task, def_id.resolved_id(), kind, cache);

        // Only run hornspec if the primary fixpoint task reported a failure.
        #[cfg(feature = "wick")]
        if !result.status.is_safe() {
            if config::dump_constraint() {
                dbg::dump_item_info(self.genv.tcx(), id, "horn", liquid_fixpoint::SmtFormatter(&hornspec_task)).unwrap();
            }
            let hs_start = std::time::Instant::now();
            let hs_safe = matches!(hornspec_task.run(), Ok(r) if r.status.is_safe());
            metrics::record(
                metrics::TimingKind::HornspecQuery { def_id: id, safe: hs_safe },
                hs_start.elapsed(),
            );
        }
        #[cfg(feature = "wick")]
        let (fixpoint_solution, solution) = self.parse_kvar_solutions(&result)?;
        #[cfg(not(feature = "wick"))]
        let (_fixpoint_solution, solution) = self.parse_kvar_solutions(&result)?;

        time_it::<QueryResult<Answer<Tag>>>(
            TimingKind::RefinementHint(def_id.as_local().unwrap()),
            || {
                #[cfg(feature = "wick")]
                for constraint in flat_constraint_map.values_mut() {
                    constraint.assumptions = constraint
                        .assumptions
                        .iter()
                        .flat_map(|pred| {
                            // Remove all trivially true assumptions
                            if pred.is_trivially_true() {
                                vec![].into_iter()
                            // Substitute the kvar solutions in
                            } else if let fixpoint::Pred::KVar(kvid, args) = pred {
                                let exprs = if let Some((sorts, solution)) =
                                    &fixpoint_solution.get(&kvid)
                                {
                                    assert!(sorts.len() == args.len());
                                    let arg_exprs = args
                                        .into_iter()
                                        .map(|arg| fixpoint::Expr::Var(*arg))
                                        .collect_vec();
                                    let subst_solution = solution.substitute_bvar(&arg_exprs, 0);
                                    subst_solution.as_conjunction().into_iter()
                                    // We'll do hoisting later when we split disjuncts.
                                } else {
                                    // println!("Missing kvar solution for kvid {:?}", kvid);
                                    vec![].into_iter()
                                };
                                exprs
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

                let errors = match result.status {
                    FixpointStatus::Safe(_) => vec![],
                    FixpointStatus::Unsafe(_, errors) => {
                        metrics::incr_metric(Metric::CsError, errors.len() as u32);
                        let tags = errors.into_iter().map(|err| err.tag).unique().collect_vec();
                        tags.into_iter()
                        .map(|tag_idx| {
                            let tag = self.tags[tag_idx];
                            let blame_ctx = self.blame_ctx_map[&tag_idx].clone();
                            #[cfg(not(feature = "wick"))]
                            let possible_solutions = FxIndexMap::default();
                            #[cfg(feature = "wick")]
                            let mut possible_solutions: FxIndexMap<rty::WKVid, Vec<rty::Binder<rty::Expr>>> = FxIndexMap::default();
                            #[cfg(feature = "wick")]
                            if let Some(flat_constraint) = flat_constraint_map.get(&tag_idx) {
                                println!(
                                    "Looking for weak kvars that might solve {}",
                                    flat_constraint.head,
                                );
                                let head_expr = match &flat_constraint.head {
                                    fixpoint::Pred::Expr(e) => Some(e.clone()),
                                    _ => None,
                                };
                                // FIXME: this should be a better source of fresh names, but 100000
                                // should be safe.
                                let mut fresh_rty_name: usize = 100_000;
                                let mut fresh_var = || {
                                    let local_var = self.ecx.local_var_env.fresh_name();
                                    let rty_var = rty::Expr::fvar(rty::Name::from_usize(fresh_rty_name));
                                    self.ecx.local_var_env.reverse_map.insert(local_var, rty_var);
                                    fresh_rty_name += 1;
                                    fixpoint::Var::Local(local_var)
                                };
                                let wkvars_and_constraints = flat_constraint.wkvars_and_constrs(&mut fresh_var);
                                // println!("There are {} wkvars/constraint pairs to try", wkvars_and_constraints.len());
                                for (wkvar, flat_constraint, other_constrs) in wkvars_and_constraints {
                                    if !other_constrs.iter().all(|other_constr| {
                                        let binder_consts = other_constr.binders.iter().map(|(var, sort)| {
                                            fixpoint::ConstDecl {
                                                name: *var,
                                                sort: sort.clone(),
                                                comment: None,
                                            }
                                        }).collect_vec();
                                        println!("checking validity in split");
                                        check_validity(&other_constr, &binder_consts, &constants_without_inequalities, data_decls.clone())

                                    }) {
                                        // println!("WARN: There is at least one non-valid constraint among {} other constraints, skipping solving...", other_constrs.len());
                                        continue;
                                    }
                                    let ConstKey::WKVar(wkvid, self_args) = self.ecx.const_env.wkvar_map_rev.get(&wkvar.wkvid).unwrap()
                                    else {
                                        panic!()
                                    };
                                    let fvars: HashSet<fixpoint::Var> = wkvar
                                        .args
                                        .iter()
                                        .flat_map(|arg| {
                                            arg.free_vars().into_iter().filter(|fvar| {
                                                match fvar {
                                                    fixpoint::Var::Local(_)
                                                    | fixpoint::Var::Param(_) => true,
                                                    _ => false,
                                                }
                                            })
                                        })
                                        .collect();
                                    let rty_args: Vec<rty::Expr> = wkvar
                                        .args
                                        .iter()
                                        .map(|arg| self.fixpoint_to_expr(arg))
                                        .try_collect().unwrap();
                                    let (binder_consts, mut new_flat_constraint) =
                                        flat_constraint.remove_binders(&fvars);
                                    // Remove any wkvars and drop assumptions that are just wkvars or true
                                    new_flat_constraint.assumptions = new_flat_constraint.assumptions.into_iter().filter_map(|assumption| {
                                        let assumption = assumption.strip_wkvars();
                                        if !assumption.is_trivially_true() {
                                            Some(assumption)
                                        } else {
                                            None
                                        }
                                    }).collect();
                                    match qe_and_simplify(&new_flat_constraint, &binder_consts, &constants_without_inequalities, data_decls.clone()) {
                                        Ok(fe) => {
                                            match self.fixpoint_to_expr(&fe) {
                                                Ok(e) => {
                                                    if !e.is_trivially_false()
                                                        && !e.is_trivially_true() {
                                                        if let Some(binder_e) = WKVarInstantiator::try_instantiate_wkvar_args(*self_args, &rty_args, &e) {
                                                            if fe.total_num_disjuncts() > 3 {
                                                                // Try the regular expression
                                                                // NOTE: previously used blame_ctx.expr
                                                                if let Some(binder_e) = WKVarInstantiator::try_instantiate_wkvar_args(*self_args, &rty_args, &self.fixpoint_to_expr(head_expr.as_ref().unwrap()).unwrap()) {
                                                                    possible_solutions.entry(wkvid.clone())
                                                                        .or_default()
                                                                        .push(binder_e);
                                                                }
                                                            } else {
                                                                possible_solutions.entry(wkvid.clone())
                                                                    .or_default()
                                                                    .push(binder_e);
                                                            }
                                                        } else {
                                                            // NOTE: previously used blame_ctx.expr
                                                            if let Some(binder_e) = WKVarInstantiator::try_instantiate_wkvar_args(*self_args, &rty_args, &self.fixpoint_to_expr(head_expr.as_ref().unwrap()).unwrap()) {
                                                                possible_solutions.entry(wkvid.clone())
                                                                    .or_default()
                                                                    .push(binder_e);
                                                            }
                                                        }
                                                    } else {
                                                        // Skipped trivial solution
                                                    }
                                                }
                                                Err(_err) => {},
                                        }
                                        }
                                        Err(_err) => {
                                            // NOTE: previously used blame_ctx.expr
                                            if let Some(binder_e) = WKVarInstantiator::try_instantiate_wkvar_args(*self_args, &rty_args, &self.fixpoint_to_expr(head_expr.as_ref().unwrap()).unwrap()) {
                                                possible_solutions.entry(wkvid.clone())
                                                    .or_default()
                                                    .push(binder_e);
                                            }
                                        }
                                    }
                                }
                            }
                            FixpointCheckError::new(
                                tag,
                                blame_ctx,
                                possible_solutions,
                            )
                        })
                        .collect_vec()
                    }
                    FixpointStatus::Crash(err) => span_bug!(def_span, "fixpoint crash: {err:?}"),
                };
                Ok(Answer { errors, solution })
            },
        )
    }

    fn parse_kvar_solutions(
        &self,
        result: &FixpointResult<TagIdx>,
    ) -> QueryResult<(FixpointSolution, Solution)> {
        let fixpoint_solution = result
            .solution
            .iter()
            .chain(&result.non_cuts_solution)
            .map(|b| self.convert_kvar_bind(b))
            .try_collect()?;
        let solution = self.fixpoint_to_kvar_solutions(&fixpoint_solution)?;
        Ok((fixpoint_solution, solution))
    }

    fn convert_solution(&self, expr: &str) -> QueryResult<(Vec<fixpoint::Sort>, fixpoint::Expr)> {
        // 1. convert str -> sexp
        let mut sexp_parser = Parser::new(expr);
        let sexp = match sexp_parser.parse() {
            Ok(sexp) => sexp,
            Err(err) => {
                tracked_span_bug!("cannot parse sexp: {expr:?}: {err:?}");
            }
        };

        // 2. convert sexp -> (binds, Expr<fixpoint_encoding::Types>)
        let mut sexp_ctx = SexpParseCtxt.into_wrapper();
        let mut sol = sexp_ctx.parse_solution(&sexp).unwrap_or_else(|err| {
            tracked_span_bug!("failed to parse solution sexp {sexp:?}: {err:?}");
        });
        parse_wkvars(&mut sol.1);
        Ok(sol)
    }

    fn convert_kvar_bind(
        &self,
        b: &liquid_fixpoint::KVarBind,
    ) -> QueryResult<(fixpoint::KVid, (Vec<fixpoint::Sort>, fixpoint::Expr))> {
        // println!("converting {}", b.dump());
        let kvid = parse_kvid(&b.kvar);
        let sol = self.convert_solution(&b.val)?;
        Ok((kvid, sol))
    }

    fn fixpoint_to_kvar_solutions(
        &self,
        fixpoint_solution: &FixpointSolution,
    ) -> QueryResult<Solution> {
        // convert Expr<fixpoint_encoding::Types> -> Expr<rty::Expr>
        // (leaving the kvids in fixpoint for now).
        let solution_only_expr_conv = fixpoint_solution
            .iter()
            .map(|(fixpoint_kvid, (sorts, expr))| {
                let sorts = sorts
                    .iter()
                    .map(|s| self.fixpoint_to_sort(s))
                    .try_collect_vec()
                    .unwrap_or_else(|err| {
                        tracked_span_bug!("failed to convert sorts: {err:?}");
                    });
                let expr = self
                    .fixpoint_to_expr(expr)
                    .unwrap_or_else(|err| tracked_span_bug!("failed to convert expr: {err:?}"));
                let binder = rty::Binder::bind_with_sorts(expr, &sorts);
                (*fixpoint_kvid, binder)
            })
            .collect_vec();

        // Convert the kvids, which requires that we group them up because there is a
        // one-to-many relation between rty::KVid and fixpoint::KVid.
        Ok(self.kcx.group_kvar_solution(solution_only_expr_conv))
    }

    pub fn generate_and_check_lean_lemmas(
        mut self,
        constraint: fixpoint::Constraint,
    ) -> QueryResult<()> {
        if let Some(def_id) = self.ecx.def_id {
            let kvar_decls = self.kcx.encode_kvars(&self.kvars, &mut self.scx);
            self.ecx.errors.to_result()?;

            let lean_encoder = LeanEncoder::new(
                self.genv,
                std::path::Path::new("./"),
                "lean_proofs".to_string(),
                "Defs".to_string(),
            );
            lean_encoder
                .encode_constraint(def_id, &kvar_decls, &constraint)
                .map_err(|_| query_bug!("could not encode constraint"))?;
            lean_encoder.check_proof(def_id)
        } else {
            Ok(())
        }
    }

    fn run_task_with_cache(
        genv: GlobalEnv,
        task: fixpoint::Task,
        def_id: DefId,
        kind: FixpointQueryKind,
        cache: &mut FixQueryCache,
    ) -> FixpointResult<TagIdx> {
        let key = kind.task_key(genv.tcx(), def_id);

        let hash = task.hash_with_default();

        if config::is_cache_enabled()
            && let Some(result) = cache.lookup(&key, hash)
        {
            metrics::incr_metric_if(kind.is_body(), Metric::FnCached);
            return result.clone();
        }
        let result = metrics::time_it(TimingKind::FixpointQuery(def_id, kind), || {
            task.run()
                .unwrap_or_else(|err| tracked_span_bug!("failed to run fixpoint: {err}"))
        });

        if config::is_cache_enabled() {
            cache.insert(key, hash, result.clone());
        }

        result
    }

    fn tag_idx(&mut self, tag: Tag) -> TagIdx
    where
        Tag: std::fmt::Debug,
    {
        // *self.tags_inv.entry(tag).or_insert_with(|| {
        let idx = self.tags.push(tag);
        self.comments.push(format!("Tag {idx}: {tag:?}"));
        idx
        // })
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
        blame_analysis: BlameAnalysis,
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
                    .map(|e| self.head_to_fixpoint(e, mk_tag, blame_analysis.clone()))
                    .try_collect()?;
                Ok(fixpoint::Constraint::conj(cstrs))
            }
            // NOTE(ck): We remove the below "optimization" to make the
            // suggestions we give better.
            //
            // Because we only presently offer fix suggestions that use
            // the constraint head, if we have an implication like
            // `a => b` as the head and we translate it to
            // `forall _ : int. a => b`, then we will only offer suggestions
            // of the form `b`. By removing this optimization, we ensure
            // that we offer suggestions of the form `a => b`, which is
            // often more desirable.
            //
            // rty::ExprKind::BinaryOp(rty::BinOp::Imp, e1, e2) => {
            //     let (bindings, assumption) =
            //         self.assumption_to_fixpoint(e1, &mut blame_analysis)?;
            //     let cstr = self.head_to_fixpoint(e2, mk_tag, blame_analysis)?;
            //     Ok(fixpoint::Constraint::foralls(bindings, mk_implies(assumption, cstr)))
            // }
            rty::ExprKind::KVar(kvar) => {
                let mut bindings = vec![];
                let pred = self.kvar_to_fixpoint(kvar, &mut bindings)?;
                Ok(fixpoint::Constraint::foralls(bindings, fixpoint::Constraint::Pred(pred, None)))
            }
            rty::ExprKind::WKVar(_wkvar) => {
                // We don't translate the weak kvar here because we don't want to
                // send it to fixpoint to check (we only care about it appearing
                // in assumptions)
                Ok(fixpoint::Constraint::TRUE)
            }
            rty::ExprKind::ForAll(pred) => {
                self.ecx
                    .local_var_env
                    .push_layer_with_fresh_names(pred.vars().len());
                let cstr =
                    self.head_to_fixpoint(pred.as_ref().skip_binder(), mk_tag, blame_analysis)?;
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
                // Extract the spans from all of the vars related to the expression
                // (including the vars in the expression).
                self.blame_ctx_map
                    .insert(tag_idx, BlameCtxt { blame_analysis, expr: expr.clone() });

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
        blame_analysis: &mut BlameAnalysis,
    ) -> QueryResult<(Vec<fixpoint::Bind>, fixpoint::Pred)> {
        // Convert assumption
        let mut bindings = vec![];
        let mut preds = vec![];

        self.assumption_to_fixpoint_aux(pred, &mut bindings, &mut preds, blame_analysis)?;
        blame_analysis
            .assumed_preds
            .extend(pred.flatten_conjs().into_iter().cloned());
        Ok((bindings, fixpoint::Pred::and(preds)))
    }

    /// Auxiliary function to merge nested conjunctions in a single predicate
    fn assumption_to_fixpoint_aux(
        &mut self,
        expr: &rty::Expr,
        bindings: &mut Vec<fixpoint::Bind>,
        preds: &mut Vec<fixpoint::Pred>,
        blame_analysis: &mut BlameAnalysis,
    ) -> QueryResult {
        match expr.kind() {
            rty::ExprKind::BinaryOp(rty::BinOp::And, e1, e2) => {
                self.assumption_to_fixpoint_aux(e1, bindings, preds, blame_analysis)?;
                self.assumption_to_fixpoint_aux(e2, bindings, preds, blame_analysis)?;
            }
            rty::ExprKind::KVar(kvar) => {
                preds.push(self.kvar_to_fixpoint(kvar, bindings)?);
            }
            rty::ExprKind::WKVar(wkvar) => {
                preds.push(self.wkvar_to_fixpoint(wkvar)?);
                blame_analysis.wkvars.push(wkvar.clone());
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
                // NOTE: We might need to figure out how to skip weak kvars if they
                // appear in the expression here because they may have free vars
                // that will screw with this analysis.
                //
                // Add binder deps.
                //
                // We assume that for each predicate in the conjunction of the
                // assumption, all of the variables in that predicate depend on
                // each other. Hence why we compute the relation in this part of
                // the assumption helper.
                //
                // E.g. for the predicate
                //
                // (a0 = Foo a1 a2) /\ (b0 > b1) /\ (b0 < a1)
                //
                // The first clause tells us {a0, a1, a2} are all interrelated.
                // The second clause tells us {b0, b1} are all interrelated.
                // The third clause tells us {b0, a1} are all interrelated.
                let fvars = expr.fvars();
                for fvar in &fvars {
                    // In the unlikely (and perhaps impossible) case that names
                    // are reused for binders, we ensure that we don't
                    // initialize the dependencies if a name is missing. Perhaps
                    // it would be better to panic/error here.
                    if let Some((_bp, _depth, deps)) = blame_analysis.binder_deps.get_mut(fvar) {
                        for fvar2 in &fvars {
                            if fvar != fvar2 {
                                deps.insert(*fvar2);
                            }
                        }
                    }
                }
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
        let kvids = self.kcx.declare(kvar.kvid, decl);

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
            return Ok(fixpoint::Pred::KVar(kvids.start, vec![var]));
        }

        let kvars = kvids
            .enumerate()
            .map(|(i, kvid)| {
                let args = all_args[i..].to_vec();
                fixpoint::Pred::KVar(kvid, args)
            })
            .collect_vec();

        Ok(fixpoint::Pred::And(kvars))
    }

    fn wkvar_to_fixpoint(&mut self, wkvar: &rty::WKVar) -> QueryResult<fixpoint::Pred> {
        if let Some(var) =
            self.ecx
                .define_const_for_wkvar(&wkvar.wkvid, wkvar.self_args, &mut self.scx)
        {
            let args: Vec<fixpoint::Expr> = wkvar
                .args
                .iter()
                .map(|arg| self.ecx.expr_to_fixpoint(arg, &mut self.scx))
                .collect::<QueryResult<Vec<fixpoint::Expr>>>()?;
            Ok(fixpoint::Pred::Expr(fixpoint::Expr::WKVar(fixpoint::WKVar { wkvid: var, args })))
        } else {
            // println!("WARN: Skipping encoding wkvar {:?} because it isn't in the global map", wkvar.wkvid);
            Ok(fixpoint::Pred::Expr(fixpoint::Expr::Constant(fixpoint::Constant::Boolean(true))))
        }
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

/// During encoding into fixpoint we generate multiple fixpoint kvars per kvar in flux. A
/// [`KVarEncodingCtxt`] is used to keep track of the state needed for this.
///
/// See [`KVarEncoding`]
#[derive(Default)]
struct KVarEncodingCtxt {
    /// A map from a [`rty::KVid`] to the range of [`fixpoint::KVid`]s that will be used to
    /// encode it.
    ranges: FxIndexMap<rty::KVid, Range<fixpoint::KVid>>,
}

impl KVarEncodingCtxt {
    /// Declares that a kvar has to be encoded into fixpoint and assigns a range of
    /// [`fixpoint::KVid`]'s to it.
    fn declare(&mut self, kvid: rty::KVid, decl: &KVarDecl) -> Range<fixpoint::KVid> {
        // The start of the next range
        let start = self
            .ranges
            .last()
            .map_or(fixpoint::KVid::from_u32(0), |(_, r)| r.end);

        self.ranges
            .entry(kvid)
            .or_insert_with(|| {
                match decl.encoding {
                    KVarEncoding::Single => start..start + 1,
                    KVarEncoding::Conj => {
                        let n = usize::max(decl.self_args, 1);
                        start..start + n
                    }
                }
            })
            .clone()
    }

    fn encode_kvars(&self, kvars: &KVarGen, scx: &mut SortEncodingCtxt) -> Vec<fixpoint::KVarDecl> {
        self.ranges
            .iter()
            .flat_map(|(orig, range)| {
                let mut all_sorts = kvars
                    .get(*orig)
                    .sorts
                    .iter()
                    .map(|s| scx.sort_to_fixpoint(s))
                    .collect_vec();

                // See comment in `kvar_to_fixpoint`
                if all_sorts.is_empty() {
                    all_sorts = vec![fixpoint::Sort::Int];
                }

                range.clone().enumerate().map(move |(i, kvid)| {
                    let sorts = all_sorts[i..].to_vec();
                    fixpoint::KVarDecl::new(kvid, sorts, format!("orig: {:?}", orig))
                })
            })
            .collect()
    }

    /// For each [`rty::KVid`] `$k`, this function collects all predicates associated
    /// with the [`fixpoint::KVid`]s that encode `$k` and combines them into a single
    /// predicate by conjoining them.
    ///
    /// A group (i.e., a combined predicate) is included in the result only if *all*
    /// [`fixpoint::KVid`]s in the encoding range of `$k` are present in the input.
    fn group_kvar_solution(
        &self,
        mut items: Vec<(fixpoint::KVid, rty::Binder<rty::Expr>)>,
    ) -> HashMap<rty::KVid, rty::Binder<rty::Expr>> {
        let mut map = HashMap::default();

        items.sort_by_key(|(kvid, _)| *kvid);
        items.reverse();

        for (orig, range) in &self.ranges {
            let mut preds = vec![];
            while let Some((_, t)) = items.pop_if(|(k, _)| range.contains(k)) {
                preds.push(t);
            }
            // We only put it in the map if the entire range is present.
            if preds.len() == range.end.as_usize() - range.start.as_usize() {
                let vars = preds[0].vars().clone();
                let conj = rty::Expr::and_from_iter(
                    preds
                        .into_iter()
                        .enumerate()
                        .map(|(i, e)| e.skip_binder().shift_horizontally(i)),
                );
                map.insert(*orig, rty::Binder::bind_with_vars(conj, vars));
            }
        }
        map
    }
}

/// Environment used to map from [`rty::Var`] to a [`fixpoint::LocalVar`].
struct LocalVarEnv {
    local_var_gen: IndexGen<fixpoint::LocalVar>,
    fvars: UnordMap<rty::Name, fixpoint::LocalVar>,
    /// Layers of late bound variables
    layers: Vec<Vec<fixpoint::LocalVar>>,
    /// While it might seem like the signature should be
    /// [`UnordMap<fixpoint::LocalVar, rty::Var>`], we encode the arguments to
    /// kvars (which can be arbitrary expressions) as local variables; thus we
    /// need to keep the output as an [`rty::Expr`] to reflect this.
    reverse_map: UnordMap<fixpoint::LocalVar, rty::Expr>,
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
        self.reverse_map.insert(fresh, rty::Expr::fvar(name));
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

#[derive(Clone)]
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

    // This function is called before we encode a constraint that will be translated to Lean.
    // It's a hack that allows us to emit fewer KVars since in Lean we are not restricting solutions
    // to predicates that use their first argument like we do in fixpoint.
    pub(crate) fn make_all_single(&mut self) {
        self.kvars
            .iter_mut()
            .for_each(|decl| decl.encoding = KVarEncoding::Single);
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
    wkvar_map_rev: HashMap<fixpoint::Var, ConstKey<'tcx>>,
    global_var_gen: IndexGen<fixpoint::GlobalVar>,
    pub fun_def_map: FunDefMap,
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

pub struct ExprEncodingCtxt<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    local_var_env: LocalVarEnv,
    const_env: ConstEnv<'tcx>,
    /// WKVar declarations collected for the hornspec backend.
    wkvars: FxIndexMap<rty::WKVid, fixpoint::WKVarDecl>,
    errors: Errors<'genv>,
    /// Id of the item being checked. This is a [`MaybeExternId`] because we may be encoding
    /// invariants for an extern spec on an enum.
    def_id: Option<MaybeExternId>,
    infcx: rustc_infer::infer::InferCtxt<'tcx>,
}

impl<'genv, 'tcx> ExprEncodingCtxt<'genv, 'tcx> {
    pub fn new(genv: GlobalEnv<'genv, 'tcx>, def_id: Option<MaybeExternId>) -> Self {
        Self {
            genv,
            local_var_env: LocalVarEnv::new(),
            const_env: Default::default(),
            wkvars: Default::default(),
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
        self.def_id
            .map_or(DUMMY_SP, |def_id| self.genv.tcx().def_span(def_id))
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
        // NOTE(ck): See note in `sort_to_fixpoint` in the case of
        // ````
        // rty::Sort::App(rty::SortCtor::Adt(sort_def), args)
        // ````
        let adt_id = scx.declare_adt(*did);
        let ctor = fixpoint::Expr::Var(fixpoint::Var::DataCtor(adt_id, VariantIdx::ZERO));
        let args = flds
            .iter()
            .map(|fld| self.expr_to_fixpoint(fld, scx))
            .try_collect()?;
        Ok(fixpoint::Expr::App(Box::new(ctor), None, args))
    }

    fn fields_to_fixpoint(
        &mut self,
        flds: &[rty::Expr],
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::Expr> {
        // NOTE(ck): See note in `sort_to_fixpoint` in the case of
        // ````
        // rty::Sort::App(rty::SortCtor::Adt(sort_def), args)
        // ````
        scx.declare_tuple(flds.len());
        let ctor = fixpoint::Expr::Var(fixpoint::Var::TupleCtor { arity: flds.len() });
        let args = flds
            .iter()
            .map(|fld| self.expr_to_fixpoint(fld, scx))
            .try_collect()?;
        Ok(fixpoint::Expr::App(Box::new(ctor), None, args))
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
                if !sort_args.is_empty() {
                    // println!("sort_args ({:?}) is not empty for val: {:?} with args {:?}" , op, sort_args, args)
                }
                let func = fixpoint::Expr::Var(self.define_const_for_prim_op(op, scx));
                let args = self.exprs_to_fixpoint(args, scx)?;
                Ok(fixpoint::Expr::App(Box::new(func), None, args))
            }
            InternalFuncKind::Rel(op) => {
                if !sort_args.is_empty() {
                    // println!("sort_args ({:?}) is not empty for rel: {:?} with args {:?}" , op, sort_args, args)
                }
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
                        Ok(fixpoint::Expr::App(Box::new(func), None, args))
                    }
                }
            }
        }
    }

    fn structurally_normalize_expr(&self, expr: &rty::Expr) -> QueryResult<rty::Expr> {
        if let Some(def_id) = self.def_id {
            structurally_normalize_expr(self.genv, def_id.resolved_id(), &self.infcx, expr)
        } else {
            Ok(expr.clone())
        }
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
                fixpoint::Expr::App(Box::new(fixpoint::Expr::Var(ctor)), None, args)
            }
            rty::ExprKind::ConstDefId(did) => {
                let var = self.define_const_for_rust_const(*did, scx);
                fixpoint::Expr::Var(var)
            }
            rty::ExprKind::App(func, sort_args, args) => {
                if let rty::ExprKind::InternalFunc(func) = func.kind() {
                    self.internal_func_to_fixpoint(func, sort_args, args, scx)?
                } else {
                    if !sort_args.is_empty() {
                        // println!("sort_args ({:?}) is not empty for expr {:?}", sort_args, expr);
                    }
                    let func = self.expr_to_fixpoint(func, scx)?;
                    let sort_args = self.sort_args_to_fixpoint(sort_args, scx);
                    let args = self.exprs_to_fixpoint(args, scx)?;
                    fixpoint::Expr::App(Box::new(func), Some(sort_args), args)
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
                fixpoint::Expr::App(Box::new(func), None, args)
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
            rty::ExprKind::WKVar(_)
            | rty::ExprKind::Hole(..)
            | rty::ExprKind::KVar(_)
            | rty::ExprKind::Local(_)
            | rty::ExprKind::PathProj(..)
            | rty::ExprKind::ForAll(_)
            | rty::ExprKind::Exists(_)
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

    fn sort_args_to_fixpoint(
        &mut self,
        sort_args: &[rty::SortArg],
        scx: &mut SortEncodingCtxt,
    ) -> Vec<fixpoint::Sort> {
        sort_args
            .iter()
            .map(|s_arg| self.sort_arg_to_fixpoint(s_arg, scx))
            .collect()
    }

    fn sort_arg_to_fixpoint(
        &mut self,
        sort_arg: &rty::SortArg,
        scx: &mut SortEncodingCtxt,
    ) -> fixpoint::Sort {
        match sort_arg {
            rty::SortArg::Sort(sort) => scx.sort_to_fixpoint(sort),
            rty::SortArg::BvSize(sz) => bv_size_to_fixpoint(*sz),
        }
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
        // NOTE(ck): See note in `sort_to_fixpoint` in the case of
        // ````
        // rty::Sort::App(rty::SortCtor::Adt(sort_def), args)
        // ````
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
        Ok(fixpoint::Expr::App(Box::new(proj), None, vec![self.expr_to_fixpoint(e, scx)?]))
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

    fn set_op_to_fixpoint(&self, op: &rty::BinOp) -> fixpoint::Expr {
        let itf = match op {
            rty::BinOp::Sub(_) => fixpoint::ThyFunc::SetDif,
            rty::BinOp::BitAnd(_) => fixpoint::ThyFunc::SetCap,
            rty::BinOp::BitOr(_) => fixpoint::ThyFunc::SetCup,
            _ => span_bug!(self.def_span(), "not a set operation!"),
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
            rty::BinOp::BitAnd(_) => fixpoint::ThyFunc::BvAnd,
            rty::BinOp::BitOr(_) => fixpoint::ThyFunc::BvOr,
            rty::BinOp::BitXor(_) => fixpoint::ThyFunc::BvXor,
            rty::BinOp::BitShl(_) => fixpoint::ThyFunc::BvShl,
            rty::BinOp::BitShr(_) => fixpoint::ThyFunc::BvLshr,
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

            // Bit vector operations
            rty::BinOp::Add(rty::Sort::BitVec(_))
            | rty::BinOp::Sub(rty::Sort::BitVec(_))
            | rty::BinOp::Mul(rty::Sort::BitVec(_))
            | rty::BinOp::Div(rty::Sort::BitVec(_))
            | rty::BinOp::Mod(rty::Sort::BitVec(_))
            | rty::BinOp::BitAnd(rty::Sort::BitVec(_))
            | rty::BinOp::BitOr(rty::Sort::BitVec(_))
            | rty::BinOp::BitXor(rty::Sort::BitVec(_))
            | rty::BinOp::BitShl(rty::Sort::BitVec(_))
            | rty::BinOp::BitShr(rty::Sort::BitVec(_)) => {
                let bv_func = self.bv_op_to_fixpoint(op);
                return Ok(fixpoint::Expr::App(
                    Box::new(bv_func),
                    None,
                    vec![self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?],
                ));
            }

            // Set operations
            rty::BinOp::Sub(rty::Sort::App(rty::SortCtor::Set, _))
            | rty::BinOp::BitAnd(rty::Sort::App(rty::SortCtor::Set, _))
            | rty::BinOp::BitOr(rty::Sort::App(rty::SortCtor::Set, _)) => {
                let set_func = self.set_op_to_fixpoint(op);
                return Ok(fixpoint::Expr::App(
                    Box::new(set_func),
                    None,
                    vec![self.expr_to_fixpoint(e1, scx)?, self.expr_to_fixpoint(e2, scx)?],
                ));
            }

            // Interpreted arithmetic operations
            rty::BinOp::Add(_) => fixpoint::BinOp::Add,
            rty::BinOp::Sub(_) => fixpoint::BinOp::Sub,
            rty::BinOp::Mul(_) => fixpoint::BinOp::Mul,
            rty::BinOp::Div(_) => fixpoint::BinOp::Div,
            rty::BinOp::Mod(_) => fixpoint::BinOp::Mod,

            rty::BinOp::BitAnd(sort)
            | rty::BinOp::BitOr(sort)
            | rty::BinOp::BitXor(sort)
            | rty::BinOp::BitShl(sort)
            | rty::BinOp::BitShr(sort) => {
                bug!("unsupported operation `{op:?}` for sort `{sort:?}`");
            }
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
                fixpoint::Expr::App(Box::new(rel), None, vec![e1, e2])
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
                    None,
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
        let farg = self.expr_to_fixpoint(arg, scx)?;
        // Check if it's a variable after encoding, in case the encoding produced a variable from a
        // non-variable.
        if let fixpoint::Expr::Var(var) = farg {
            Ok(var)
        } else {
            let fresh = self.local_var_env.fresh_name();
            self.local_var_env.reverse_map.insert(fresh, arg.clone());
            let pred = fixpoint::Expr::eq(fixpoint::Expr::Var(fresh.into()), farg);
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
    pub fn declare_fun(&mut self, def_id: FluxDefId) -> fixpoint::Var {
        *self.const_env.fun_def_map.entry(def_id).or_insert_with(|| {
            let id = self.const_env.global_var_gen.fresh();
            fixpoint::Var::Global(id, Some(def_id.name()))
        })
    }

    /// The logic below is a bit "duplicated" with the `prim_op_sort` in `sortck.rs`;
    /// They are not exactly the same because this is on rty and the other one on fhir.
    /// We should make sure these two remain in sync.
    ///
    /// (NOTE:PrimOpSort) We are somewhat "overloading" the `BinOps`: as we are using them
    /// for (a) interpreted operations on bit vectors AND (b) uninterpreted functions on integers.
    /// So when Binop::BitShr (a) appears in a ExprKind::BinOp, it means bit vectors, but
    /// (b) inside ExprKind::InternalFunc it means int.
    fn prim_op_sort(op: &rty::BinOp, span: Span) -> rty::PolyFuncSort {
        match op {
            rty::BinOp::BitAnd(rty::Sort::Int)
            | rty::BinOp::BitOr(rty::Sort::Int)
            | rty::BinOp::BitXor(rty::Sort::Int)
            | rty::BinOp::BitShl(rty::Sort::Int)
            | rty::BinOp::BitShr(rty::Sort::Int) => {
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

    /// We encode weak kvars as UIFs when we send them to fixpoint, but
    /// represent them in fixpoint as their own Expr. This is necessary to add
    /// the const declaration for the UIF.
    ///
    /// Currently returns an Option in case weak kvars generated automatically
    /// don't track the sorts of their arguments, but there is no reason why
    /// they shouldn't --- we could probably unwrap the Option.
    fn define_const_for_wkvar(
        &mut self,
        wkvid: &rty::WKVid,
        self_args: usize,
        scx: &mut SortEncodingCtxt,
    ) -> Option<fixpoint::Var> {
        if !wkvid.parent_fn.is_local() {
            // println!("INFO: skipping encoding {} because it is not local", _wkvid_string);
            return None;
        }
        let key = ConstKey::WKVar(wkvid.clone(), self_args);
        let arg_sorts = self
            .genv
            .weak_kvars_for(wkvid.parent_fn)
            .and_then(|wkvars_map| {
                wkvars_map
                    .get(&wkvid.id.as_u32())
                    .map(|wkvars| wkvars.sorts.clone())
            });
        arg_sorts.map(|arg_sorts| {
            self.const_env
                .const_map
                .entry(key.clone())
                .or_insert_with(|| {
                    let comment = Some(format!("weak kvar: {:?}", wkvid));
                    let def_name = self.genv.tcx().def_path_str(wkvid.parent_fn);
                    let sanitized_name: String = def_name
                        .chars()
                        .map(|c| if !c.is_alphanumeric() { '_' } else { c })
                        .collect();
                    let name =
                        fixpoint::Var::WKVar(Symbol::intern(&sanitized_name), wkvid.id.as_u32());
                    let func_sort = rty::FuncSort::new(arg_sorts.clone(), rty::Sort::Bool).to_poly();
                    let sort = scx.func_sort_to_fixpoint(&func_sort);
                    self.const_env.wkvar_map_rev.insert(name, key);
                    // Also record as WKVarDecl for hornspec backend
                    self.wkvars.entry(wkvid.clone()).or_insert_with(|| {
                        let sorts = arg_sorts.iter().map(|s| scx.sort_to_fixpoint(s)).collect_vec();
                        fixpoint::WKVarDecl { wkvid: name, comment: format!("weak kvar: {:?}", name), sorts }
                    });
                    fixpoint::ConstDecl { name, comment, sort }
                })
                .name
        })
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
        while let Some((&did, _)) = self.const_env.fun_def_map.get_index(idx) {
            idx += 1;

            let info = self.genv.normalized_info(did);
            let revealed = reveals.contains(&did);
            if info.hide && !revealed && !proven_externally {
                consts.push(self.fun_decl_to_fixpoint(did, scx));
            } else {
                defs.push((info.rank, self.fun_def_to_fixpoint(did, scx)?));
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

    pub fn fun_decl_to_fixpoint(
        &mut self,
        def_id: FluxDefId,
        scx: &mut SortEncodingCtxt,
    ) -> fixpoint::ConstDecl {
        let name = self.const_env.fun_def_map[&def_id];
        let sort = scx.func_sort_to_fixpoint(&self.genv.func_sort(def_id));
        fixpoint::ConstDecl { name, sort, comment: Some(format!("flux def: {def_id:?}")) }
    }

    pub fn fun_def_to_fixpoint(
        &mut self,
        def_id: FluxDefId,
        scx: &mut SortEncodingCtxt,
    ) -> QueryResult<fixpoint::FunDef> {
        let name = *self.const_env.fun_def_map.get(&def_id).unwrap();
        let info = self.genv.normalized_info(def_id);
        let out = scx.sort_to_fixpoint(self.genv.func_sort(def_id).expect_mono().output());
        let (args, body) = self.body_to_fixpoint(&info.body, scx)?;
        Ok(fixpoint::FunDef {
            name,
            args,
            body,
            out,
            comment: Some(format!("flux def: {def_id:?}")),
        })
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

fn parse_kvid(kvid: &str) -> fixpoint::KVid {
    if kvid.starts_with("k")
        && let Some(kvid) = kvid[1..].parse::<u32>().ok()
    {
        fixpoint::KVid::from_u32(kvid)
    } else {
        tracked_span_bug!("unexpected kvar name {kvid}")
    }
}

fn parse_local_var(name: &str) -> Option<fixpoint::Var> {
    if let Some(rest) = name.strip_prefix('a')
        && let Ok(idx) = rest.parse::<u32>()
    {
        return Some(fixpoint::Var::Local(fixpoint::LocalVar::from(idx)));
    }
    None
}

fn parse_global_var(name: &str) -> Option<fixpoint::Var> {
    if let Some(rest) = name.strip_prefix('c')
        && let Ok(idx) = rest.parse::<u32>()
    {
        return Some(fixpoint::Var::Global(fixpoint::GlobalVar::from(idx), None));
    }
    // try parsing as a named global variable
    if let Some(rest) = name.strip_prefix("f$")
        && let parts = rest.split('$').collect::<Vec<_>>()
        && parts.len() == 2
        && let Ok(global_idx) = parts[1].parse::<u32>()
    {
        return Some(fixpoint::Var::Global(
            fixpoint::GlobalVar::from(global_idx),
            Some(Symbol::intern(parts[0])),
        ));
    }
    None
}

fn parse_param(name: &str) -> Option<fixpoint::Var> {
    if let Some(rest) = name.strip_prefix("reftgen$")
        && let parts = rest.split('$').collect::<Vec<_>>()
        && parts.len() == 2
        && let Ok(index) = parts[1].parse::<u32>()
    {
        let name = Symbol::intern(parts[0]);
        let param = EarlyReftParam { index, name };
        return Some(fixpoint::Var::Param(param));
    }
    None
}

fn parse_data_proj(name: &str) -> Option<fixpoint::Var> {
    if let Some(rest) = name.strip_prefix("fld")
        && let parts = rest.split('$').collect::<Vec<_>>()
        && parts.len() == 2
        && let Ok(adt_id) = parts[0].parse::<u32>()
        && let Ok(field) = parts[1].parse::<u32>()
    {
        let adt_id = fixpoint::AdtId::from(adt_id);
        return Some(fixpoint::Var::DataProj { adt_id, field });
    }
    None
}

fn parse_data_ctor(name: &str) -> Option<fixpoint::Var> {
    if let Some(rest) = name.strip_prefix("mkadt")
        && let parts = rest.split('$').collect::<Vec<_>>()
        && parts.len() == 2
        && let Ok(adt_id) = parts[0].parse::<u32>()
        && let Ok(variant_idx) = parts[1].parse::<u32>()
    {
        let adt_id = fixpoint::AdtId::from(adt_id);
        let variant_idx = VariantIdx::from(variant_idx);
        return Some(fixpoint::Var::DataCtor(adt_id, variant_idx));
    }
    None
}

fn parse_weak_kvar(name: &str) -> Option<fixpoint::Var> {
    if let Some(rest) = name.strip_prefix("wk$")
        && let parts = rest.split('$').collect::<Vec<_>>()
        && parts.len() == 2
        && let Ok(index) = parts[1].parse::<u32>()
    {
        let name = Symbol::intern(parts[0]);
        return Some(fixpoint::Var::WKVar(name, index));
    }
    None
}

struct SexpParseCtxt;

impl FromSexp<FixpointTypes> for SexpParseCtxt {
    fn kvar(&self, name: &str) -> Result<fixpoint::KVid, ParseError> {
        bug!("TODO: SexpParse: kvar: {name}")
    }

    fn string(&self, s: &str) -> Result<fixpoint::SymStr, ParseError> {
        Ok(fixpoint::SymStr(Symbol::intern(s)))
    }

    fn var(&self, name: &str) -> Result<fixpoint::Var, ParseError> {
        if let Some(var) = parse_local_var(name) {
            return Ok(var);
        }
        if let Some(var) = parse_global_var(name) {
            return Ok(var);
        }
        if let Some(var) = parse_weak_kvar(name) {
            return Ok(var);
        }
        if let Some(var) = parse_param(name) {
            return Ok(var);
        }
        if let Some(var) = parse_data_proj(name) {
            return Ok(var);
        }
        if let Some(var) = parse_data_ctor(name) {
            return Ok(var);
        }
        Err(ParseError::err(format!("Unknown variable: {name}")))
    }

    fn sort(&self, name: &str) -> Result<fixpoint::DataSort, ParseError> {
        if let Some(idx) = name.strip_prefix("Adt")
            && let Ok(adt_id) = idx.parse::<u32>()
        {
            return Ok(fixpoint::DataSort::Adt(fixpoint::AdtId::from(adt_id)));
        }
        Err(ParseError::err(format!("Unknown sort: {name}")))
    }
}

fn parse_wkvars(expr: &mut fixpoint::Expr) {
    use fixpoint::*;
    match expr {
        Expr::Constant(_) | Expr::ThyFunc(_) | Expr::Var(_) => {}
        Expr::App(head, _sort_args, args) => {
            match &mut **head {
                Expr::Var(v @ Var::WKVar(..)) => {
                    *expr = Expr::WKVar(WKVar { wkvid: *v, args: args.clone() });
                }
                e => {
                    parse_wkvars(e);
                }
            }
        }
        Expr::Neg(e) | Expr::Not(e) => parse_wkvars(e),
        Expr::BinaryOp(_, exprs) | Expr::Imp(exprs) | Expr::Iff(exprs) | Expr::Atom(_, exprs) => {
            let [e1, e2] = &mut **exprs;
            parse_wkvars(e1);
            parse_wkvars(e2);
        }
        Expr::IfThenElse(exprs) => {
            let [p, e1, e2] = &mut **exprs;
            parse_wkvars(p);
            parse_wkvars(e1);
            parse_wkvars(e2);
        }
        Expr::And(exprs) | Expr::Or(exprs) => {
            for e in exprs {
                parse_wkvars(e);
            }
        }
        Expr::Let(_, exprs) => {
            let [var_e, body_e] = &mut **exprs;
            parse_wkvars(var_e);
            parse_wkvars(body_e);
        }
        Expr::IsCtor(_v, expr) => {
            parse_wkvars(expr);
        }
        Expr::Exists(_binder, expr) => {
            parse_wkvars(expr);
        }
        Expr::WKVar(fixpoint::WKVar { wkvid: _, args }) => {
            for e in args {
                parse_wkvars(e);
            }
        }
        Expr::BoundVar(..) => {}
    }
}

/// Post-processing pass that flattens ADT/Tuple sorts into scalars for the hornspec backend.
///
/// Single-constructor ADTs and tuples are isomorphic to the product of their fields.
/// This pass exploits that by expanding each ADT-typed position (ForAll binding, KVar argument)
/// into multiple scalar positions — one per leaf field. Constructors and projections are
/// eliminated: constructors become argument splicing, projections become leaf-variable selection.
mod adt_flatten {
    use std::collections::HashMap;

    use super::fixpoint::{self, DataSort, LocalVar, Var};
    use liquid_fixpoint::{
        Bind, Constraint, DataDecl, Expr, KVarDecl, Pred, Sort, SortCtor, WKVarDecl,
    };

    type FixTypes = fixpoint::fixpoint_generated::FixpointTypes;

    /// For each DataSort, stores the leaf sorts that it flattens to.
    struct FlatLayout {
        leaves: HashMap<DataSort, Vec<Sort<FixTypes>>>,
        field_ranges: HashMap<(DataSort, u32), (usize, usize)>,
    }

    impl FlatLayout {
        fn build(data_decls: &[DataDecl<FixTypes>]) -> Self {
            let mut leaves: HashMap<DataSort, Vec<Sort<FixTypes>>> = HashMap::new();
            let mut field_ranges: HashMap<(DataSort, u32), (usize, usize)> = HashMap::new();

            let mut changed = true;
            while changed {
                changed = false;
                for decl in data_decls {
                    if leaves.contains_key(&decl.name) {
                        continue;
                    }
                    if decl.ctors.len() != 1 {
                        panic!(
                            "adt_flatten: multi-constructor ADT {:?} not supported for hornspec",
                            decl.name
                        );
                    }
                    let ctor = &decl.ctors[0];
                    let mut all_resolved = true;
                    let mut decl_leaves = Vec::new();
                    let mut decl_field_ranges = Vec::new();
                    for (i, field) in ctor.fields.iter().enumerate() {
                        let offset = decl_leaves.len();
                        match Self::leaf_sorts_of(&field.sort, &leaves) {
                            Some(field_leaves) => {
                                let width = field_leaves.len();
                                decl_leaves.extend(field_leaves);
                                decl_field_ranges.push((i as u32, offset, width));
                            }
                            None => {
                                all_resolved = false;
                                break;
                            }
                        }
                    }
                    if all_resolved {
                        for (field, offset, width) in decl_field_ranges {
                            field_ranges.insert((decl.name.clone(), field), (offset, width));
                        }
                        leaves.insert(decl.name.clone(), decl_leaves);
                        changed = true;
                    }
                }
            }

            for decl in data_decls {
                if !leaves.contains_key(&decl.name) {
                    panic!(
                        "adt_flatten: could not resolve flat layout for {:?} \
                         (recursive ADTs are not supported)",
                        decl.name
                    );
                }
            }

            FlatLayout { leaves, field_ranges }
        }

        fn leaf_sorts_of(
            sort: &Sort<FixTypes>,
            known: &HashMap<DataSort, Vec<Sort<FixTypes>>>,
        ) -> Option<Vec<Sort<FixTypes>>> {
            match sort {
                Sort::App(SortCtor::Data(ds), _args) => known.get(ds).cloned(),
                _ => Some(vec![sort.clone()]),
            }
        }

        fn flatten_sort(&self, sort: &Sort<FixTypes>) -> Vec<Sort<FixTypes>> {
            match sort {
                Sort::App(SortCtor::Data(ds), _args) => {
                    self.leaves
                        .get(ds)
                        .unwrap_or_else(|| {
                            panic!("adt_flatten: unknown DataSort {ds:?} during flatten_sort")
                        })
                        .clone()
                }
                _ => vec![sort.clone()],
            }
        }

        fn is_adt_sort(&self, sort: &Sort<FixTypes>) -> bool {
            matches!(sort, Sort::App(SortCtor::Data(ds), _) if self.leaves.contains_key(ds))
        }

        fn field_range(&self, ds: &DataSort, field: u32) -> (usize, usize) {
            *self
                .field_ranges
                .get(&(ds.clone(), field))
                .unwrap_or_else(|| panic!("adt_flatten: no field range for ({ds:?}, {field})"))
        }
    }

    #[derive(Clone)]
    struct VarExpansion {
        leaf_vars: Vec<LocalVar>,
    }

    struct Flattener {
        layout: FlatLayout,
        var_map: HashMap<Var, VarExpansion>,
        next_local: u32,
    }

    impl Flattener {
        fn fresh_local(&mut self) -> LocalVar {
            let v = LocalVar::from_u32(self.next_local);
            self.next_local += 1;
            v
        }

        fn expand_binding(
            &mut self,
            name: Var,
            sort: &Sort<FixTypes>,
        ) -> Vec<(Var, Sort<FixTypes>)> {
            let leaf_sorts = self.layout.flatten_sort(sort);
            if leaf_sorts.len() == 1 && !self.layout.is_adt_sort(sort) {
                return vec![(name, sort.clone())];
            }
            let mut leaf_vars = Vec::with_capacity(leaf_sorts.len());
            let mut bindings = Vec::with_capacity(leaf_sorts.len());
            for leaf_sort in &leaf_sorts {
                let lv = self.fresh_local();
                leaf_vars.push(lv);
                bindings.push((Var::Local(lv), leaf_sort.clone()));
            }
            self.var_map.insert(name, VarExpansion { leaf_vars });
            bindings
        }

        fn expr_to_leaves(&self, expr: Expr<FixTypes>) -> Vec<Expr<FixTypes>> {
            match expr {
                Expr::Var(ref v) => {
                    if let Some(expansion) = self.var_map.get(v) {
                        expansion
                            .leaf_vars
                            .iter()
                            .map(|lv| Expr::Var(Var::Local(*lv)))
                            .collect()
                    } else {
                        vec![expr]
                    }
                }
                // Our App is (func, sort_args, args) — 3 fields (no out_sort)
                Expr::App(func, sort_args, args) => {
                    match *func {
                        Expr::Var(Var::DataProj { adt_id, field }) => {
                            assert_eq!(args.len(), 1, "DataProj should have exactly 1 argument");
                            let inner_leaves =
                                self.expr_to_leaves(args.into_iter().next().unwrap());
                            let ds = DataSort::Adt(adt_id);
                            let (offset, width) = self.layout.field_range(&ds, field);
                            inner_leaves[offset..offset + width].to_vec()
                        }
                        Expr::Var(Var::TupleProj { arity, field }) => {
                            assert_eq!(args.len(), 1, "TupleProj should have exactly 1 argument");
                            let inner_leaves =
                                self.expr_to_leaves(args.into_iter().next().unwrap());
                            let ds = DataSort::Tuple(arity);
                            let (offset, width) = self.layout.field_range(&ds, field);
                            inner_leaves[offset..offset + width].to_vec()
                        }
                        Expr::Var(Var::DataCtor(..)) => {
                            args.into_iter().flat_map(|a| self.expr_to_leaves(a)).collect()
                        }
                        Expr::Var(Var::TupleCtor { .. }) => {
                            args.into_iter().flat_map(|a| self.expr_to_leaves(a)).collect()
                        }
                        other_func => {
                            let func = Box::new(self.rewrite_scalar_expr(other_func));
                            let args =
                                args.into_iter().map(|a| self.rewrite_scalar_expr(a)).collect();
                            vec![Expr::App(func, sort_args, args)]
                        }
                    }
                }
                Expr::IsCtor(_, _) => {
                    vec![Expr::Constant(liquid_fixpoint::Constant::Boolean(true))]
                }
                other => vec![self.rewrite_scalar_expr(other)],
            }
        }

        fn rewrite_scalar_expr(&self, expr: Expr<FixTypes>) -> Expr<FixTypes> {
            match expr {
                Expr::Var(ref v) => {
                    if self.var_map.contains_key(v) {
                        panic!(
                            "adt_flatten: ADT variable {v:?} used in scalar context \
                             (expected projection or KVar arg)"
                        );
                    }
                    expr
                }
                Expr::App(..) => {
                    let leaves = self.expr_to_leaves(expr);
                    assert_eq!(
                        leaves.len(),
                        1,
                        "adt_flatten: App expression in scalar context produced multiple leaves"
                    );
                    leaves.into_iter().next().unwrap()
                }
                Expr::IsCtor(_, _) => Expr::Constant(liquid_fixpoint::Constant::Boolean(true)),
                Expr::Constant(_) | Expr::ThyFunc(_) | Expr::BoundVar(_) => expr,
                Expr::Neg(e) => Expr::Neg(Box::new(self.rewrite_scalar_expr(*e))),
                Expr::Not(e) => Expr::Not(Box::new(self.rewrite_scalar_expr(*e))),
                Expr::BinaryOp(op, operands) => {
                    let [e1, e2] = *operands;
                    Expr::BinaryOp(
                        op,
                        Box::new([self.rewrite_scalar_expr(e1), self.rewrite_scalar_expr(e2)]),
                    )
                }
                Expr::Imp(operands) => {
                    let [e1, e2] = *operands;
                    Expr::Imp(Box::new([
                        self.rewrite_scalar_expr(e1),
                        self.rewrite_scalar_expr(e2),
                    ]))
                }
                Expr::Iff(operands) => {
                    let [e1, e2] = *operands;
                    Expr::Iff(Box::new([
                        self.rewrite_scalar_expr(e1),
                        self.rewrite_scalar_expr(e2),
                    ]))
                }
                Expr::Atom(rel, operands) => {
                    let [e1, e2] = *operands;
                    let leaves1 = self.expr_to_leaves(e1);
                    let leaves2 = self.expr_to_leaves(e2);
                    if leaves1.len() == 1 && leaves2.len() == 1 {
                        Expr::Atom(
                            rel,
                            Box::new([
                                leaves1.into_iter().next().unwrap(),
                                leaves2.into_iter().next().unwrap(),
                            ]),
                        )
                    } else {
                        assert_eq!(
                            leaves1.len(),
                            leaves2.len(),
                            "adt_flatten: mismatched ADT comparison widths"
                        );
                        Expr::And(
                            leaves1
                                .into_iter()
                                .zip(leaves2)
                                .map(|(l, r)| Expr::Atom(rel, Box::new([l, r])))
                                .collect(),
                        )
                    }
                }
                Expr::IfThenElse(operands) => {
                    let [p, e1, e2] = *operands;
                    Expr::IfThenElse(Box::new([
                        self.rewrite_scalar_expr(p),
                        self.rewrite_scalar_expr(e1),
                        self.rewrite_scalar_expr(e2),
                    ]))
                }
                Expr::And(es) => {
                    Expr::And(es.into_iter().map(|e| self.rewrite_scalar_expr(e)).collect())
                }
                Expr::Or(es) => {
                    Expr::Or(es.into_iter().map(|e| self.rewrite_scalar_expr(e)).collect())
                }
                Expr::Let(var, exprs) => {
                    let [init, body] = *exprs;
                    Expr::Let(
                        var,
                        Box::new([self.rewrite_scalar_expr(init), self.rewrite_scalar_expr(body)]),
                    )
                }
                Expr::Exists(sorts, body) => {
                    // Our Exists has anonymous sort-only binders (no var names)
                    let new_sorts: Vec<_> = sorts
                        .into_iter()
                        .flat_map(|s| self.layout.flatten_sort(&s))
                        .collect();
                    Expr::Exists(new_sorts, Box::new(self.rewrite_scalar_expr(*body)))
                }
                Expr::WKVar(wkvar) => {
                    let args = wkvar
                        .args
                        .into_iter()
                        .flat_map(|a| self.expr_to_leaves(a))
                        .collect();
                    Expr::WKVar(liquid_fixpoint::WKVar { wkvid: wkvar.wkvid, args })
                }
            }
        }

        fn rewrite_pred(&self, pred: Pred<FixTypes>) -> Pred<FixTypes> {
            match pred {
                Pred::And(preds) => {
                    Pred::And(preds.into_iter().map(|p| self.rewrite_pred(p)).collect())
                }
                Pred::KVar(kvid, args) => {
                    // Our Pred::KVar args are Vec<T::Var>, not Vec<Expr<T>>.
                    // Expand any ADT-typed var references via var_map.
                    let new_args: Vec<Var> = args
                        .into_iter()
                        .flat_map(|v| {
                            if let Some(expansion) = self.var_map.get(&v) {
                                expansion.leaf_vars.iter().map(|lv| Var::Local(*lv)).collect()
                            } else {
                                vec![v]
                            }
                        })
                        .collect();
                    Pred::KVar(kvid, new_args)
                }
                Pred::Expr(e) => Pred::Expr(self.rewrite_scalar_expr(e)),
            }
        }

        fn rewrite_constraint(&mut self, cstr: Constraint<FixTypes>) -> Constraint<FixTypes> {
            match cstr {
                Constraint::Pred(pred, tag) => Constraint::Pred(self.rewrite_pred(pred), tag),
                Constraint::Conj(cstrs) => {
                    Constraint::Conj(cstrs.into_iter().map(|c| self.rewrite_constraint(c)).collect())
                }
                Constraint::ForAll(bind, inner) => {
                    if self.layout.is_adt_sort(&bind.sort) {
                        let expanded = self.expand_binding(bind.name, &bind.sort);
                        let pred = self.rewrite_pred(bind.pred);
                        let inner = self.rewrite_constraint(*inner);
                        expanded.into_iter().rev().fold(inner, |acc, (var, sort)| {
                            Constraint::ForAll(
                                Bind { name: var, sort, pred: pred.clone() },
                                Box::new(acc),
                            )
                        })
                    } else {
                        let pred = self.rewrite_pred(bind.pred);
                        let inner = self.rewrite_constraint(*inner);
                        Constraint::ForAll(
                            Bind { name: bind.name, sort: bind.sort, pred },
                            Box::new(inner),
                        )
                    }
                }
            }
        }
    }

    fn find_max_local(task: &fixpoint::Task) -> u32 {
        let mut max_local: u32 = 0;

        fn scan_var(v: &Var, max: &mut u32) {
            if let Var::Local(lv) = v {
                *max = (*max).max(lv.as_u32());
            }
        }

        fn scan_expr(e: &Expr<FixTypes>, max: &mut u32) {
            match e {
                Expr::Var(v) => scan_var(v, max),
                Expr::App(func, _, args) => {
                    scan_expr(func, max);
                    args.iter().for_each(|a| scan_expr(a, max));
                }
                Expr::Neg(e) | Expr::Not(e) | Expr::IsCtor(_, e) => scan_expr(e, max),
                Expr::BinaryOp(_, es) | Expr::Imp(es) | Expr::Iff(es) | Expr::Atom(_, es) => {
                    es.iter().for_each(|e| scan_expr(e, max));
                }
                Expr::IfThenElse(es) => es.iter().for_each(|e| scan_expr(e, max)),
                Expr::And(es) | Expr::Or(es) => es.iter().for_each(|e| scan_expr(e, max)),
                Expr::Let(v, es) => {
                    scan_var(v, max);
                    es.iter().for_each(|e| scan_expr(e, max));
                }
                Expr::Exists(_sorts, body) => {
                    // Our Exists has anonymous sorts only (no bound var names to scan)
                    scan_expr(body, max);
                }
                Expr::WKVar(wk) => {
                    scan_var(&wk.wkvid, max);
                    wk.args.iter().for_each(|a| scan_expr(a, max));
                }
                Expr::Constant(_) | Expr::ThyFunc(_) | Expr::BoundVar(_) => {}
            }
        }

        fn scan_pred(p: &Pred<FixTypes>, max: &mut u32) {
            match p {
                Pred::And(ps) => ps.iter().for_each(|p| scan_pred(p, max)),
                // Our Pred::KVar args are Vec<Var>, not Vec<Expr>
                Pred::KVar(_, args) => args.iter().for_each(|a| scan_var(a, max)),
                Pred::Expr(e) => scan_expr(e, max),
            }
        }

        fn scan_constraint(c: &Constraint<FixTypes>, max: &mut u32) {
            match c {
                Constraint::Pred(p, _) => scan_pred(p, max),
                Constraint::Conj(cs) => cs.iter().for_each(|c| scan_constraint(c, max)),
                Constraint::ForAll(bind, inner) => {
                    scan_var(&bind.name, max);
                    scan_pred(&bind.pred, max);
                    scan_constraint(inner, max);
                }
            }
        }

        scan_constraint(&task.constraint, &mut max_local);
        max_local
    }

    pub fn flatten_task(mut task: fixpoint::Task) -> fixpoint::Task {
        if task.data_decls.is_empty() {
            return task;
        }

        let layout = FlatLayout::build(&task.data_decls);
        let next_local = find_max_local(&task) + 1;

        let mut flattener = Flattener { layout, var_map: HashMap::new(), next_local };

        task.kvars = task
            .kvars
            .into_iter()
            .map(|kvar| {
                let sorts = kvar
                    .sorts
                    .into_iter()
                    .flat_map(|s| flattener.layout.flatten_sort(&s))
                    .collect();
                KVarDecl { kvid: kvar.kvid, sorts, comment: kvar.comment }
            })
            .collect();

        task.wkvars = task
            .wkvars
            .into_iter()
            .map(|wkvar| {
                let sorts = wkvar
                    .sorts
                    .into_iter()
                    .flat_map(|s| flattener.layout.flatten_sort(&s))
                    .collect();
                WKVarDecl { wkvid: wkvar.wkvid, sorts, comment: wkvar.comment }
            })
            .collect();

        task.constraint = flattener.rewrite_constraint(task.constraint);
        task.data_decls.clear();

        task
    }
}

