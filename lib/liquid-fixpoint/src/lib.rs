//! This crate implements an interface to the [liquid-fixpoint] binary
//!
//! [liquid-fixpoint]: https://github.com/ucsd-progsys/liquid-fixpoint

mod constraint;

use std::{
    collections::hash_map::DefaultHasher,
    fmt::{self, Write as FmtWrite},
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
use itertools::Itertools;
use pad_adapter::PadAdapter;
use serde::{de, Deserialize};

use crate::constraint::DEFAULT_QUALIFIERS;

pub trait FixpointFmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    /// Returns a type that implements [`Display`] using the [`FixpointFmt::fmt`] implementation.
    ///
    /// [`Display`]: std::fmt::Display
    fn display(&self) -> DisplayAdapter<&Self> {
        DisplayAdapter(self)
    }
}

/// Helper type that implements [`Display`] forwarding the implementation to [`FixpointFmt::fmt`].
///
/// [`Display`]: std::fmt::Display
pub struct DisplayAdapter<T>(T);

impl<T: FixpointFmt> std::fmt::Display for DisplayAdapter<&T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        FixpointFmt::fmt(self.0, f)
    }
}

pub trait Identifier: FixpointFmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<T: Identifier> FixpointFmt for T {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Identifier::fmt(self, f)
    }
}

pub trait Types {
    type Sort: Identifier + Hash + Clone;
    type KVar: Identifier + Hash;
    type Var: Identifier + Hash;

    type Numeral: FixpointFmt + Hash;
    type Decimal: FixpointFmt + Hash;
    type String: FixpointFmt + Hash;

    type Tag: fmt::Display + FromStr + Hash;
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

#[derive(Deserialize, Debug)]
#[serde(tag = "tag", content = "contents", bound(deserialize = "Tag: FromStr"))]
pub enum FixpointResult<Tag> {
    Safe(Stats),
    Unsafe(Stats, Vec<Error<Tag>>),
    Crash(CrashInfo),
}

#[derive(Debug)]
pub struct Error<Tag> {
    pub id: i32,
    pub tag: Tag,
}

#[derive(Debug, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct Stats {
    pub num_cstr: i32,
    pub num_iter: i32,
    pub num_chck: i32,
    pub num_vald: i32,
}

#[expect(dead_code, reason = "false positive: the field is read in the `Debug` impl")]
#[derive(Deserialize, Debug)]
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
            .spawn()
            .unwrap();
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

impl<T: Types> fmt::Display for Task<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.scrape_quals {
            writeln!(f, "(fixpoint \"--scrape=both\")")?;
        }
        for line in &self.comments {
            writeln!(f, ";; {line}")?;
        }
        writeln!(f)?;

        for data_decl in &self.data_decls {
            writeln!(f, "{data_decl}")?;
        }

        for qualif in DEFAULT_QUALIFIERS.iter() {
            writeln!(f, "{qualif}")?;
        }

        for qualif in &self.qualifiers {
            writeln!(f, "{qualif}")?;
        }

        for cinfo in &self.constants {
            writeln!(f, "{cinfo}")?;
        }

        for kvar in &self.kvars {
            writeln!(f, "{kvar}")?;
        }

        writeln!(f)?;
        write!(f, "(constraint")?;
        write!(with_padding(f), "\n{}", self.constraint)?;
        writeln!(f, "\n)")
    }
}

impl<T: Types> fmt::Display for KVarDecl<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(var ${} ({})) ;; {}",
            self.kvid.display(),
            self.sorts.iter().format(" "),
            self.comment
        )
    }
}

impl<T: Types> fmt::Display for ConstDecl<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(constant {} {})", self.name.display(), self.sort)?;
        if let Some(comment) = &self.comment {
            write!(f, "  ;; {comment}")?;
        }
        Ok(())
    }
}

impl<T: Types> fmt::Debug for Task<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<'de, Tag: FromStr> Deserialize<'de> for Error<Tag> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct ErrorInner<'a>(i32, &'a str);

        let ErrorInner(id, tag) = Deserialize::deserialize(deserializer)?;
        let tag = tag
            .parse()
            .map_err(|_| de::Error::invalid_value(de::Unexpected::Str(tag), &"valid tag"))?;
        Ok(Error { id, tag })
    }
}

fn with_padding<'a, 'b>(f: &'a mut fmt::Formatter<'b>) -> PadAdapter<'a, 'b, 'static> {
    PadAdapter::with_padding(f, "  ")
}
