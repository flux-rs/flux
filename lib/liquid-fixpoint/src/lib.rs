//! This crate implements an interface to the [liquid-fixpoint] binary
//!
//! [liquid-fixpoint]: https://github.com/ucsd-progsys/liquid-fixpoint

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
use serde::{de, Deserialize, Serialize};

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
        if *self < 0 {
            write!(f, "(- {})", self.unsigned_abs())
        } else {
            write!(f, "{self}")
        }
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
