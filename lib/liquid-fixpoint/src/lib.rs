//! This crate implements an interface to the [liquid-fixpoint] binary
//!
//! [liquid-fixpoint]: https://github.com/ucsd-progsys/liquid-fixpoint
#![cfg_attr(feature = "nightly", feature(rustc_private))]

#[cfg(feature = "nightly")]
extern crate rustc_data_structures;
#[cfg(feature = "nightly")]
extern crate rustc_macros;
#[cfg(feature = "nightly")]
extern crate rustc_serialize;
#[cfg(feature = "nightly")]
extern crate rustc_span;

mod constraint;
#[cfg(feature = "rust-fixpoint")]
mod constraint_fragments;
#[cfg(feature = "rust-fixpoint")]
mod constraint_solving;
#[cfg(any(feature = "rust-fixpoint", feature = "suggestions"))]
mod constraint_with_env;
#[cfg(any(feature = "rust-fixpoint", feature = "suggestions"))]
mod cstr2smt2;
mod format;
#[cfg(any(feature = "rust-fixpoint", feature = "suggestions"))]
mod graph;
pub mod parser;
pub mod sexp;
pub mod smt_horn;
#[cfg(feature = "suggestions")]
mod z3_process;

use std::{
    collections::{HashMap, hash_map::DefaultHasher},
    fmt::{self, Debug},
    hash::{Hash, Hasher},
    io,
    str::FromStr,
};
#[cfg(not(feature = "rust-fixpoint"))]
use std::{
    io::{BufWriter, Write as IOWrite},
    process::{Command, Stdio},
};

pub use constraint::{
    BinOp, BinRel, Bind, Constant, Constraint, DataCtor, DataDecl, DataField, Expr, FlatConstraint,
    FunSort, Pred, QualParam, Qualifier, Quantifier, Sort, SortCtor, SortDecl, WKVar,
};
use derive_where::derive_where;
#[cfg(feature = "nightly")]
use rustc_macros::{Decodable, Encodable};
use serde::{Deserialize, Serialize, de};

/// Type alias for qualifier assignments used in constraint solving
pub type Assignments<'a, T> = HashMap<<T as Types>::KVar, Vec<(&'a Qualifier<T>, Vec<usize>)>>;

#[cfg(feature = "rust-fixpoint")]
use crate::constraint_with_env::ConstraintWithEnv;
#[cfg(feature = "suggestions")]
use crate::constraint_with_env::topo_sort_data_declarations;
#[cfg(feature = "suggestions")]
pub use crate::z3_process::SuggestionSolverError;

#[cfg(feature = "suggestions")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuggestionComparisonOperation {
    Qe,
    Validity,
}

#[cfg(feature = "suggestions")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuggestionComparisonOutcome {
    Agreed,
    ProcessFailed,
    BindingsFailed,
    BothFailed,
    Different,
    ComparisonFailed,
}

#[cfg(feature = "suggestions")]
#[derive(Debug)]
pub struct SuggestionComparisonEvent {
    pub operation: SuggestionComparisonOperation,
    pub outcome: SuggestionComparisonOutcome,
    pub bindings_time: std::time::Duration,
    pub process_time: std::time::Duration,
    pub details: Option<String>,
}

#[cfg(feature = "suggestions")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuggestionsZ3Backend {
    Bindings,
    Process,
    Compare,
}

#[cfg(feature = "suggestions")]
pub struct SuggestionSolver {
    backend: SuggestionsZ3Backend,
    process: Option<z3_process::ProcessSolver>,
    comparison_events: Vec<SuggestionComparisonEvent>,
}

#[cfg(feature = "suggestions")]
impl SuggestionSolver {
    pub fn new(backend: SuggestionsZ3Backend) -> Result<Self, SuggestionSolverError> {
        let process = match backend {
            SuggestionsZ3Backend::Bindings => None,
            SuggestionsZ3Backend::Process | SuggestionsZ3Backend::Compare => {
                Some(z3_process::ProcessSolver::new(backend == SuggestionsZ3Backend::Compare)?)
            }
        };
        Ok(Self { backend, process, comparison_events: Vec::new() })
    }

    pub fn take_comparison_events(&mut self) -> Vec<SuggestionComparisonEvent> {
        std::mem::take(&mut self.comparison_events)
    }
}

pub trait Types {
    type Sort: Identifier + Hash + Clone + Debug + Eq;
    type KVar: Identifier + Hash + Clone + Debug + Eq;
    type Var: Identifier + Hash + Clone + Debug + Eq;
    type String: FixpointFmt + Hash + Clone + Debug + Eq;
    type Real: FixpointFmt + Hash + Clone + Debug + Eq;
    type Tag: fmt::Display + FromStr + Hash + Clone + Debug;
}

pub trait FixpointFmt: Sized {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    /// Returns a type that implements [`fmt::Display`] using this [`FixpointFmt::fmt`] implementation.
    fn display(&self) -> impl fmt::Display {
        struct DisplayAdapter<T>(T);
        impl<T: FixpointFmt> std::fmt::Display for DisplayAdapter<&T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                FixpointFmt::fmt(self.0, f)
            }
        }
        DisplayAdapter(self)
    }
}

pub trait Identifier: Sized {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    /// Returns a type that implements [`fmt::Display`] using this [`Identifier::fmt`] implementation.
    fn display(&self) -> impl fmt::Display {
        struct DisplayAdapter<T>(T);
        impl<T: Identifier> fmt::Display for DisplayAdapter<&T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                Identifier::fmt(self.0, f)
            }
        }
        DisplayAdapter(self)
    }
}

impl Identifier for &str {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl FixpointFmt for u32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl FixpointFmt for String {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{self}\"")
    }
}

#[macro_export]
macro_rules! declare_types {
    (   type Sort = $sort:ty;
        type KVar = $kvar:ty;
        type Var = $var:ty;
        type String = $str:ty;
        type Real = $real:ty;
        type Tag = $tag:ty;
    ) => {
        pub mod fixpoint_generated {
            pub struct FixpointTypes;
            pub type Expr = $crate::Expr<FixpointTypes>;
            pub type Constraint = $crate::Constraint<FixpointTypes>;
            pub type FlatConstraint = $crate::FlatConstraint<FixpointTypes>;
            pub type KVarDecl = $crate::KVarDecl<FixpointTypes>;
            pub type ConstDecl = $crate::ConstDecl<FixpointTypes>;
            pub type FunDef = $crate::FunDef<FixpointTypes>;
            pub type FunSort = $crate::FunSort<FixpointTypes>;
            pub type FunBody = $crate::FunBody<FixpointTypes>;
            pub type Task = $crate::Task<FixpointTypes>;
            pub type Qualifier = $crate::Qualifier<FixpointTypes>;
            pub type QualParam = $crate::QualParam<FixpointTypes>;
            pub type Sort = $crate::Sort<FixpointTypes>;
            pub type SortCtor = $crate::SortCtor<FixpointTypes>;
            pub type SortDecl = $crate::SortDecl<FixpointTypes>;
            pub type DataDecl = $crate::DataDecl<FixpointTypes>;
            pub type DataCtor = $crate::DataCtor<FixpointTypes>;
            pub type DataField = $crate::DataField<FixpointTypes>;
            pub type Bind = $crate::Bind<FixpointTypes>;
            pub type Constant = $crate::Constant<FixpointTypes>;
            pub type Pred = $crate::Pred<FixpointTypes>;
            pub use $crate::{BinOp, BinRel, Quantifier, ThyFunc, WKVar};
        }

        impl $crate::Types for fixpoint_generated::FixpointTypes {
            type Sort = $sort;
            type KVar = $kvar;
            type Var = $var;
            type String = $str;
            type Real = $real;
            type Tag = $tag;
        }
    };
}

#[cfg(feature = "suggestions")]
pub fn qe_and_simplify<T: Types>(
    solver: &mut SuggestionSolver,
    constraint: &FlatConstraint<T>,
    binder_consts: &Vec<ConstDecl<T>>,
    global_consts: &Vec<ConstDecl<T>>,
    datatype_decls: Vec<DataDecl<T>>,
) -> Result<Expr<T>, SuggestionSolverError> {
    // let mut consts = self.constants.clone();
    // consts.extend(free_vars.clone());
    let datatype_decls = topo_sort_data_declarations(datatype_decls);
    let process = |solver: &mut SuggestionSolver| {
        solver
            .process
            .as_mut()
            .expect("process backend initialized")
            .qe_and_simplify(constraint, binder_consts, global_consts, &datatype_decls)
    };
    match solver.backend {
        SuggestionsZ3Backend::Bindings => {
            cstr2smt2::qe_and_simplify(constraint, binder_consts, global_consts, &datatype_decls)
                .map_err(|err| SuggestionSolverError::Bindings(format!("{err:?}")))
        }
        SuggestionsZ3Backend::Process => process(solver),
        SuggestionsZ3Backend::Compare => {
            let start = std::time::Instant::now();
            let bindings = cstr2smt2::qe_and_simplify(
                constraint,
                binder_consts,
                global_consts,
                &datatype_decls,
            )
            .map_err(|err| SuggestionSolverError::Bindings(format!("{err:?}")));
            let bindings_time = start.elapsed();
            let start = std::time::Instant::now();
            let process_result = process(solver);
            let process_time = start.elapsed();
            let (outcome, details) = match (&bindings, &process_result) {
                (Ok(lhs), Ok(rhs)) => {
                    match z3_process::equivalent(
                        solver
                            .process
                            .as_mut()
                            .expect("process backend initialized"),
                        lhs,
                        rhs,
                        constraint,
                        binder_consts,
                        global_consts,
                        &datatype_decls,
                    ) {
                        Ok(true) => (SuggestionComparisonOutcome::Agreed, None),
                        Ok(false) => {
                            (
                                SuggestionComparisonOutcome::Different,
                                Some(suggestion_comparison_details(
                                    constraint,
                                    binder_consts,
                                    global_consts,
                                    &datatype_decls,
                                    &format!("bindings:\n{lhs:#?}\nprocess:\n{rhs:#?}"),
                                    solver.process.as_ref().unwrap().last_query(),
                                )),
                            )
                        }
                        Err(_) => (SuggestionComparisonOutcome::ComparisonFailed, None),
                    }
                }
                (Ok(_), Err(_)) => (SuggestionComparisonOutcome::ProcessFailed, None),
                (Err(_), Ok(_)) => (SuggestionComparisonOutcome::BindingsFailed, None),
                (Err(_), Err(_)) => (SuggestionComparisonOutcome::BothFailed, None),
            };
            solver.comparison_events.push(SuggestionComparisonEvent {
                operation: SuggestionComparisonOperation::Qe,
                outcome,
                bindings_time,
                process_time,
                details,
            });
            process_result
        }
    }
}

#[cfg(feature = "suggestions")]
fn suggestion_comparison_details<T: Types>(
    constraint: &FlatConstraint<T>,
    binder_consts: &[ConstDecl<T>],
    global_consts: &[ConstDecl<T>],
    datatype_decls: &[DataDecl<T>],
    difference: &str,
    process_query: &str,
) -> String {
    format!(
        "constraint:\n{constraint:#?}\nbinders:\n{binder_consts:#?}\nglobal constants:\n{global_consts:#?}\ndatatypes:\n{datatype_decls:#?}\n{difference}\nprocess query:\n{process_query}"
    )
}

#[cfg(feature = "suggestions")]
pub fn check_validity<T: Types>(
    solver: &mut SuggestionSolver,
    constraint: &FlatConstraint<T>,
    binder_consts: &Vec<ConstDecl<T>>,
    global_consts: &Vec<ConstDecl<T>>,
    datatype_decls: Vec<DataDecl<T>>,
) -> Result<bool, SuggestionSolverError> {
    let datatype_decls = topo_sort_data_declarations(datatype_decls);
    let bindings =
        || Ok(cstr2smt2::check_validity(constraint, binder_consts, global_consts, &datatype_decls));
    let process = |solver: &mut SuggestionSolver| {
        solver
            .process
            .as_mut()
            .expect("process backend initialized")
            .check_validity(constraint, binder_consts, global_consts, &datatype_decls)
    };
    match solver.backend {
        SuggestionsZ3Backend::Bindings => bindings(),
        SuggestionsZ3Backend::Process => process(solver),
        SuggestionsZ3Backend::Compare => {
            let start = std::time::Instant::now();
            let bindings = bindings();
            let bindings_time = start.elapsed();
            let start = std::time::Instant::now();
            let process_result = process(solver);
            let process_time = start.elapsed();
            let (outcome, details) = match (&bindings, &process_result) {
                (Ok(lhs), Ok(rhs)) if lhs == rhs => (SuggestionComparisonOutcome::Agreed, None),
                (Ok(lhs), Ok(rhs)) => {
                    (
                        SuggestionComparisonOutcome::Different,
                        Some(suggestion_comparison_details(
                            constraint,
                            binder_consts,
                            global_consts,
                            &datatype_decls,
                            &format!("bindings: {lhs}\nprocess: {rhs}"),
                            solver.process.as_ref().unwrap().last_query(),
                        )),
                    )
                }
                (Ok(_), Err(_)) => (SuggestionComparisonOutcome::ProcessFailed, None),
                (Err(_), Ok(_)) => (SuggestionComparisonOutcome::BindingsFailed, None),
                (Err(_), Err(_)) => (SuggestionComparisonOutcome::BothFailed, None),
            };
            solver.comparison_events.push(SuggestionComparisonEvent {
                operation: SuggestionComparisonOperation::Validity,
                outcome,
                bindings_time,
                process_time,
                details,
            });
            process_result
        }
    }
}

#[derive_where(Hash, Clone, Debug)]
pub struct ConstDecl<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
    #[derive_where(skip)]
    pub comment: Option<String>,
}

#[derive_where(Hash, Debug)]
pub struct FunDef<T: Types> {
    pub name: T::Var,
    pub sort: FunSort<T>,
    pub body: Option<FunBody<T>>,
    #[derive_where(skip)]
    pub comment: Option<String>,
}

#[derive_where(Hash, Debug)]
pub struct FunBody<T: Types> {
    pub args: Vec<T::Var>,
    pub expr: Expr<T>,
}

#[derive_where(Hash)]
pub struct Task<T: Types> {
    #[derive_where(skip)]
    pub comments: Vec<String>,
    pub constants: Vec<ConstDecl<T>>,
    pub data_decls: Vec<DataDecl<T>>,
    pub define_funs: Vec<FunDef<T>>,
    pub kvars: Vec<KVarDecl<T>>,
    pub constraint: Constraint<T>,
    pub qualifiers: Vec<Qualifier<T>>,
    pub scrape_quals: bool,
    pub solver: SmtSolver,
}

#[derive(Clone, Copy, Hash)]
pub enum SmtSolver {
    Z3,
    CVC5,
}

impl fmt::Display for SmtSolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtSolver::Z3 => write!(f, "z3"),
            SmtSolver::CVC5 => write!(f, "cvc5"),
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(
    tag = "tag",
    content = "contents",
    bound(deserialize = "Tag: FromStr", serialize = "Tag: ToString")
)]
pub enum FixpointStatus<Tag> {
    Safe(Stats),
    Unsafe(Stats, Vec<Error<Tag>>),
    Crash(CrashInfo),
}

#[derive(Serialize, Deserialize, Debug, Clone, Default)]
#[serde(tag = "tag", content = "contents")]
pub enum LeanStatus {
    #[default]
    Invalid,
    Valid,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(bound(deserialize = "Tag: FromStr", serialize = "Tag: ToString"))]
pub struct VerificationResult<Tag> {
    pub status: FixpointStatus<Tag>,
    pub solution: Vec<KVarBind>,
    #[serde(rename = "nonCutsSolution")]
    pub non_cuts_solution: Vec<KVarBind>,
    #[serde(default)]
    pub lean_status: LeanStatus,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct KVarBind {
    pub kvar: String,
    pub val: String,
}

impl KVarBind {
    pub fn dump(&self) -> String {
        format!("{} := {}", self.kvar, self.val)
    }
}

impl<Tag> FixpointStatus<Tag> {
    pub fn is_safe(&self) -> bool {
        matches!(self, FixpointStatus::Safe(_))
    }

    pub fn merge(self, other: FixpointStatus<Tag>) -> Self {
        use FixpointStatus as FR;
        match (self, other) {
            (FR::Safe(stats1), FR::Safe(stats2)) => FR::Safe(stats1.merge(&stats2)),
            (FR::Safe(stats1), FR::Unsafe(stats2, errors)) => {
                FR::Unsafe(stats1.merge(&stats2), errors)
            }
            (FR::Unsafe(stats1, mut errors1), FR::Unsafe(stats2, errors2)) => {
                errors1.extend(errors2);
                FR::Unsafe(stats1.merge(&stats2), errors1)
            }
            (FR::Unsafe(stats1, errors), FR::Safe(stats2)) => {
                FR::Unsafe(stats1.merge(&stats2), errors)
            }
            (FR::Crash(info1), FR::Crash(info2)) => FR::Crash(info1.merge(info2)),
            (FR::Crash(info), _) => FR::Crash(info),
            (_, FR::Crash(info)) => FR::Crash(info),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Error<Tag> {
    pub id: i32,
    pub tag: Tag,
}

#[derive(Debug, Serialize, Deserialize, Default, Clone)]
#[serde(rename_all = "camelCase")]
pub struct Stats {
    pub num_cstr: i32,
    pub num_iter: i32,
    pub num_chck: i32,
    pub num_vald: i32,
}

impl Stats {
    pub fn merge(&self, other: &Stats) -> Self {
        Stats {
            num_cstr: self.num_cstr + other.num_cstr,
            num_iter: self.num_iter + other.num_iter,
            num_chck: self.num_chck + other.num_chck,
            num_vald: self.num_vald + other.num_vald,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct CrashInfo(Vec<serde_json::Value>);

impl CrashInfo {
    pub fn merge(self, other: CrashInfo) -> Self {
        let mut v = self.0;
        v.extend(other.0);
        CrashInfo(v)
    }
}

#[derive_where(Debug, Clone, Hash)]
pub struct KVarDecl<T: Types> {
    pub kvid: T::KVar,
    pub sorts: Vec<Sort<T>>,
    #[derive_where(skip)]
    pub comment: String,
}

impl<T: Types> Task<T> {
    pub fn hash_with_default(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    #[cfg(feature = "rust-fixpoint")]
    pub fn run(&self) -> io::Result<VerificationResult<T::Tag>> {
        let mut cstr_with_env = ConstraintWithEnv::new(
            self.data_decls.clone(),
            self.kvars.clone(),
            self.qualifiers.clone(),
            self.constants.clone(),
            self.constraint.clone(),
        );
        Ok(VerificationResult {
            status: cstr_with_env.is_satisfiable(),
            solution: vec![],
            non_cuts_solution: vec![],
            lean_status: LeanStatus::default(),
        })
    }

    #[cfg(not(feature = "rust-fixpoint"))]
    pub fn run(&self) -> io::Result<VerificationResult<T::Tag>> {
        let mut child = Command::new("fixpoint")
            .arg("-q")
            .arg("--stdin")
            .arg("--sorted-solution")
            .arg("--json")
            .arg("--allowho")
            .arg("--allowhoqs")
            .arg(format!("--solver={}", self.solver))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        let mut stdin = None;
        std::mem::swap(&mut stdin, &mut child.stdin);
        {
            let mut w = BufWriter::new(stdin.unwrap());
            // Use compact formatting to reduce overhead when communicating with fixpoint
            writeln!(w, "{}", format::CompactTask(self))?;
        }
        let out = child.wait_with_output()?;

        serde_json::from_slice(&out.stdout).map_err(|err| {
            // If we fail to parse stdout fixpoint may have outputed something to stderr
            // so use that for the error instead
            if !out.stderr.is_empty() {
                let stderr = std::str::from_utf8(&out.stderr)
                    .unwrap_or("fixpoint exited with a non-zero return code");
                io::Error::other(stderr)
            } else {
                err.into()
            }
        })
    }
}

impl<T: Types> KVarDecl<T> {
    pub fn new(kvid: T::KVar, sorts: Vec<Sort<T>>, comment: String) -> Self {
        Self { kvid, sorts, comment }
    }
}

#[derive(Serialize, Deserialize)]
struct ErrorInner(i32, String);

impl<Tag: ToString> Serialize for Error<Tag> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        ErrorInner(self.id, self.tag.to_string()).serialize(serializer)
    }
}

impl<'de, Tag: FromStr> Deserialize<'de> for Error<Tag> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let ErrorInner(id, tag) = Deserialize::deserialize(deserializer)?;
        let tag = tag
            .parse()
            .map_err(|_| de::Error::invalid_value(de::Unexpected::Str(&tag), &"valid tag"))?;
        Ok(Error { id, tag })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[cfg_attr(feature = "nightly", derive(Encodable, Decodable))]
pub enum ThyFunc {
    // STRINGS
    StrLen,
    StrConcat,
    StrPrefixOf,
    StrSuffixOf,
    StrContains,

    // BIT VECTORS
    BvZeroExtend(u8),
    BvSignExtend(u8),
    IntToBv8,
    Bv8ToInt,
    IntToBv32,
    Bv32ToInt,
    IntToBv64,
    Bv64ToInt,
    IntToBv128,
    Bv128ToInt,
    BvUle,
    BvSle,
    BvUge,
    BvSge,
    BvUdiv,
    BvSdiv,
    BvSrem,
    BvUrem,
    BvLshr,
    BvAshr,
    BvAnd,
    BvOr,
    BvXor,
    BvNot,
    BvAdd,
    BvNeg,
    BvSub,
    BvMul,
    BvShl,
    BvUgt,
    BvSgt,
    BvUlt,
    BvSlt,

    // SETS
    /// Make an empty set
    SetEmpty,
    /// Make a singleton set
    SetSng,
    /// Set union
    SetCup,
    /// Set intersection
    SetCap,
    /// Set difference
    SetDif,
    /// Subset
    SetSub,
    /// Set membership
    SetMem,

    // MAPS
    /// Create a map where all keys point to a value
    MapDefault,
    /// Select a key in a map
    MapSelect,
    /// Store a key value pair in a map
    MapStore,
}

impl ThyFunc {
    pub const ALL: [ThyFunc; 46] = [
        ThyFunc::StrLen,
        ThyFunc::StrConcat,
        ThyFunc::StrPrefixOf,
        ThyFunc::StrSuffixOf,
        ThyFunc::StrContains,
        ThyFunc::IntToBv8,
        ThyFunc::Bv8ToInt,
        ThyFunc::IntToBv32,
        ThyFunc::Bv32ToInt,
        ThyFunc::IntToBv64,
        ThyFunc::Bv64ToInt,
        ThyFunc::IntToBv128,
        ThyFunc::Bv128ToInt,
        ThyFunc::BvAdd,
        ThyFunc::BvNeg,
        ThyFunc::BvSub,
        ThyFunc::BvShl,
        ThyFunc::BvLshr,
        ThyFunc::BvAshr,
        ThyFunc::BvMul,
        ThyFunc::BvUdiv,
        ThyFunc::BvSdiv,
        ThyFunc::BvUrem,
        ThyFunc::BvSrem,
        ThyFunc::BvAnd,
        ThyFunc::BvOr,
        ThyFunc::BvXor,
        ThyFunc::BvNot,
        ThyFunc::BvUle,
        ThyFunc::BvSle,
        ThyFunc::BvUge,
        ThyFunc::BvSge,
        ThyFunc::BvUgt,
        ThyFunc::BvSgt,
        ThyFunc::BvUlt,
        ThyFunc::BvSlt,
        ThyFunc::SetEmpty,
        ThyFunc::SetSng,
        ThyFunc::SetCup,
        ThyFunc::SetMem,
        ThyFunc::SetCap,
        ThyFunc::SetDif,
        ThyFunc::SetSub,
        ThyFunc::MapDefault,
        ThyFunc::MapSelect,
        ThyFunc::MapStore,
    ];
}

impl fmt::Display for ThyFunc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ThyFunc::StrLen => write!(f, "strLen"),
            ThyFunc::StrConcat => write!(f, "strConcat"),
            ThyFunc::StrPrefixOf => write!(f, "strPrefixOf"),
            ThyFunc::StrSuffixOf => write!(f, "strSuffixOf"),
            ThyFunc::StrContains => write!(f, "strContains"),
            ThyFunc::BvZeroExtend(size) => {
                // `app` is a hack in liquid-fixpoint used to implement indexed identifiers
                write!(f, "app (_ zero_extend {size})")
            }
            ThyFunc::BvSignExtend(size) => write!(f, "app (_ sign_extend {size})"),
            ThyFunc::IntToBv32 => write!(f, "int_to_bv32"),
            ThyFunc::Bv32ToInt => write!(f, "bv32_to_int"),
            ThyFunc::IntToBv8 => write!(f, "int_to_bv8"),
            ThyFunc::Bv8ToInt => write!(f, "bv8_to_int"),
            ThyFunc::IntToBv64 => write!(f, "int_to_bv64"),
            ThyFunc::Bv64ToInt => write!(f, "bv64_to_int"),
            ThyFunc::IntToBv128 => write!(f, "int_to_bv128"),
            ThyFunc::Bv128ToInt => write!(f, "bv128_to_int"),
            ThyFunc::BvUle => write!(f, "bvule"),
            ThyFunc::BvSle => write!(f, "bvsle"),
            ThyFunc::BvUge => write!(f, "bvuge"),
            ThyFunc::BvSge => write!(f, "bvsge"),
            ThyFunc::BvUdiv => write!(f, "bvudiv"),
            ThyFunc::BvSdiv => write!(f, "bvsdiv"),
            ThyFunc::BvUrem => write!(f, "bvurem"),
            ThyFunc::BvSrem => write!(f, "bvsrem"),
            ThyFunc::BvLshr => write!(f, "bvlshr"),
            ThyFunc::BvAshr => write!(f, "bvashr"),
            ThyFunc::BvAnd => write!(f, "bvand"),
            ThyFunc::BvOr => write!(f, "bvor"),
            ThyFunc::BvXor => write!(f, "bvxor"),
            ThyFunc::BvNot => write!(f, "bvnot"),
            ThyFunc::BvAdd => write!(f, "bvadd"),
            ThyFunc::BvNeg => write!(f, "bvneg"),
            ThyFunc::BvSub => write!(f, "bvsub"),
            ThyFunc::BvMul => write!(f, "bvmul"),
            ThyFunc::BvShl => write!(f, "bvshl"),
            ThyFunc::BvUgt => write!(f, "bvugt"),
            ThyFunc::BvSgt => write!(f, "bvsgt"),
            ThyFunc::BvUlt => write!(f, "bvult"),
            ThyFunc::BvSlt => write!(f, "bvslt"),
            ThyFunc::SetEmpty => write!(f, "Set_empty"),
            ThyFunc::SetSng => write!(f, "Set_sng"),
            ThyFunc::SetCup => write!(f, "Set_cup"),
            ThyFunc::SetCap => write!(f, "Set_cap"),
            ThyFunc::SetDif => write!(f, "Set_dif"),
            ThyFunc::SetMem => write!(f, "Set_mem"),
            ThyFunc::SetSub => write!(f, "Set_sub"),
            ThyFunc::MapDefault => write!(f, "Map_default"),
            ThyFunc::MapSelect => write!(f, "Map_select"),
            ThyFunc::MapStore => write!(f, "Map_store"),
        }
    }
}

impl FromStr for ThyFunc {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "strLen" => Ok(ThyFunc::StrLen),
            "int_to_bv32" => Ok(ThyFunc::IntToBv32),
            "bv32_to_int" => Ok(ThyFunc::Bv32ToInt),
            "int_to_bv8" => Ok(ThyFunc::IntToBv8),
            "bv8_to_int" => Ok(ThyFunc::Bv8ToInt),
            "int_to_bv64" => Ok(ThyFunc::IntToBv64),
            "bv64_to_int" => Ok(ThyFunc::Bv64ToInt),
            "int_to_bv128" => Ok(ThyFunc::IntToBv128),
            "bv128_to_int" => Ok(ThyFunc::Bv128ToInt),
            "bvule" => Ok(ThyFunc::BvUle),
            "bvsle" => Ok(ThyFunc::BvSle),
            "bvuge" => Ok(ThyFunc::BvUge),
            "bvsge" => Ok(ThyFunc::BvSge),
            "bvudiv" => Ok(ThyFunc::BvUdiv),
            "bvsdiv" => Ok(ThyFunc::BvSdiv),
            "bvurem" => Ok(ThyFunc::BvUrem),
            "bvsrem" => Ok(ThyFunc::BvSrem),
            "bvlshr" => Ok(ThyFunc::BvLshr),
            "bvashr" => Ok(ThyFunc::BvAshr),
            "bvand" => Ok(ThyFunc::BvAnd),
            "bvor" => Ok(ThyFunc::BvOr),
            "bvxor" => Ok(ThyFunc::BvXor),
            "bvnot" => Ok(ThyFunc::BvNot),
            "bvadd" => Ok(ThyFunc::BvAdd),
            "bvneg" => Ok(ThyFunc::BvNeg),
            "bvsub" => Ok(ThyFunc::BvSub),
            "bvmul" => Ok(ThyFunc::BvMul),
            "bvshl" => Ok(ThyFunc::BvShl),
            "bvugt" => Ok(ThyFunc::BvUgt),
            "bvsgt" => Ok(ThyFunc::BvSgt),
            "bvult" => Ok(ThyFunc::BvUlt),
            "bvslt" => Ok(ThyFunc::BvSlt),
            "Set_empty" => Ok(ThyFunc::SetEmpty),
            "Set_sng" => Ok(ThyFunc::SetSng),
            "Set_cup" => Ok(ThyFunc::SetCup),
            "Set_mem" => Ok(ThyFunc::SetMem),
            "Map_default" => Ok(ThyFunc::MapDefault),
            "Map_select" => Ok(ThyFunc::MapSelect),
            "Map_store" => Ok(ThyFunc::MapStore),
            // TODO: (ck) Fix this?
            // NOTE: (ck) There isn't a straightforward way to translate
            // the name of a Z3 node to the BvZeroExtend and BvSignExtend,
            // so this is a partial parse.
            _ => Err(format!("Unexpected ThyFunc {}", s)),
        }
    }
}
