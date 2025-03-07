//! This crate implements an interface to the [liquid-fixpoint] binary
//!
//! [liquid-fixpoint]: https://github.com/ucsd-progsys/liquid-fixpoint
#![cfg_attr(feature = "nightly", feature(rustc_private))]

#[cfg(feature = "nightly")]
extern crate rustc_macros;
#[cfg(feature = "nightly")]
extern crate rustc_serialize;
#[cfg(feature = "nightly")]
extern crate rustc_span;

mod constraint;
mod format;

use std::{
    collections::hash_map::DefaultHasher,
    fmt,
    hash::{Hash, Hasher},
    io::{self, BufWriter, Write as IOWrite},
    process::{Command, Stdio},
    str::FromStr,
};

pub use constraint::{
    BinOp, BinRel, Bind, Constant, Constraint, DataCtor, DataDecl, DataField, Expr, Pred,
    Qualifier, Sort, SortCtor,
};
use derive_where::derive_where;
#[cfg(feature = "nightly")]
use rustc_macros::{Decodable, Encodable};
use serde::{Deserialize, Serialize, de};

pub trait Types {
    type Sort: Identifier + Hash + Clone;
    type KVar: Identifier + Hash;
    type Var: Identifier + Hash;
    type Numeral: FixpointFmt + Hash;
    type Decimal: FixpointFmt + Hash;
    type String: FixpointFmt + Hash;
    type Tag: fmt::Display + FromStr + Hash;
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

struct DefaultTypes;

impl Types for DefaultTypes {
    type Sort = &'static str;
    type KVar = &'static str;
    type Var = &'static str;
    type Tag = String;
    type Numeral = i128;
    type Decimal = i128;
    type String = String;
}

impl Identifier for &str {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl FixpointFmt for i128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self < 0 { write!(f, "(- {})", self.unsigned_abs()) } else { write!(f, "{self}") }
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
        type Numeral = $int:ty;
        type Decimal = $real:ty;
        type String = $str:ty;

        type Tag = $tag:ty;
    ) => {
        pub mod fixpoint_generated {
            pub struct FixpointTypes;
            pub type Expr = $crate::Expr<FixpointTypes>;
            pub type Pred = $crate::Pred<FixpointTypes>;
            pub type Constraint = $crate::Constraint<FixpointTypes>;
            pub type KVarDecl = $crate::KVarDecl<FixpointTypes>;
            pub type ConstDecl = $crate::ConstDecl<FixpointTypes>;
            pub type Task = $crate::Task<FixpointTypes>;
            pub type Qualifier = $crate::Qualifier<FixpointTypes>;
            pub type Sort = $crate::Sort<FixpointTypes>;
            pub type SortCtor = $crate::SortCtor<FixpointTypes>;
            pub type DataDecl = $crate::DataDecl<FixpointTypes>;
            pub type DataCtor = $crate::DataCtor<FixpointTypes>;
            pub type DataField = $crate::DataField<FixpointTypes>;
            pub type Bind = $crate::Bind<FixpointTypes>;
            pub type Constant = $crate::Constant<FixpointTypes>;
            pub use $crate::{BinOp, BinRel};
        }

        impl $crate::Types for fixpoint_generated::FixpointTypes {
            type Sort = $sort;
            type KVar = $kvar;
            type Var = $var;

            type Numeral = $int;
            type Decimal = $real;
            type String = $str;

            type Tag = $tag;
        }
    };
}

#[derive_where(Hash)]
pub struct ConstDecl<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
    #[derive_where(skip)]
    pub comment: Option<String>,
}

#[derive_where(Hash)]
pub struct Task<T: Types> {
    #[derive_where(skip)]
    pub comments: Vec<String>,
    pub constants: Vec<ConstDecl<T>>,
    pub data_decls: Vec<DataDecl<T>>,
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
pub enum FixpointResult<Tag> {
    Safe(Stats),
    Unsafe(Stats, Vec<Error<Tag>>),
    Crash(CrashInfo),
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

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct CrashInfo(Vec<serde_json::Value>);

#[derive_where(Hash)]
pub struct KVarDecl<T: Types> {
    kvid: T::KVar,
    sorts: Vec<Sort<T>>,
    #[derive_where(skip)]
    comment: String,
}

impl<T: Types> Task<T> {
    pub fn hash_with_default(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    pub fn run(&self) -> io::Result<FixpointResult<T::Tag>> {
        let mut child = Command::new("fixpoint")
            .arg("-q")
            .arg("--stdin")
            .arg("--json")
            .arg("--allowho")
            .arg("--allowhoqs")
            .arg(format!("--solver={}", self.solver))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let mut stdin = None;
        std::mem::swap(&mut stdin, &mut child.stdin);
        {
            let mut w = BufWriter::new(stdin.unwrap());
            writeln!(w, "{self}")?;
        }
        let out = child.wait_with_output()?;

        let result = serde_json::from_slice(&out.stdout)?;

        Ok(result)
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

    // BIT VECTORS
    BvZeroExtend(u8),
    BvSignExtend(u8),
    IntToBv32,
    Bv32ToInt,
    IntToBv64,
    Bv64ToInt,
    BvUle,
    BvSle,
    BvUge,
    BvSge,
    BvUdiv,
    BvSdiv,
    BvUmod,
    BvSmod,
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
    pub const ALL: [ThyFunc; 37] = [
        ThyFunc::StrLen,
        ThyFunc::IntToBv32,
        ThyFunc::Bv32ToInt,
        ThyFunc::IntToBv64,
        ThyFunc::Bv64ToInt,
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
        ThyFunc::BvUmod,
        ThyFunc::BvSmod,
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
        ThyFunc::MapDefault,
        ThyFunc::MapSelect,
        ThyFunc::MapStore,
    ];
}

impl fmt::Display for ThyFunc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ThyFunc::StrLen => write!(f, "strLen"),
            ThyFunc::BvZeroExtend(size) => {
                // `app` is a hack in liquid-fixpoint used to implement indexed identifiers
                write!(f, "app (_ zero_extend {size})")
            }
            ThyFunc::BvSignExtend(size) => write!(f, "app (_ sign_extend {size})"),
            ThyFunc::IntToBv32 => write!(f, "int_to_bv32"),
            ThyFunc::Bv32ToInt => write!(f, "bv32_to_int"),
            ThyFunc::IntToBv64 => write!(f, "int_to_bv64"),
            ThyFunc::Bv64ToInt => write!(f, "bv64_to_int"),
            ThyFunc::BvUle => write!(f, "bvule"),
            ThyFunc::BvSle => write!(f, "bvsle"),
            ThyFunc::BvUge => write!(f, "bvuge"),
            ThyFunc::BvSge => write!(f, "bvsge"),
            ThyFunc::BvUdiv => write!(f, "bvudiv"),
            ThyFunc::BvSdiv => write!(f, "bvsdiv"),
            ThyFunc::BvUmod => write!(f, "bvumod"),
            ThyFunc::BvSmod => write!(f, "bvsmod"),
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
            ThyFunc::SetMem => write!(f, "Set_mem"),
            ThyFunc::MapDefault => write!(f, "Map_default"),
            ThyFunc::MapSelect => write!(f, "Map_select"),
            ThyFunc::MapStore => write!(f, "Map_store"),
        }
    }
}
