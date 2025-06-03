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

// Make format module public if it contains publicly used items like Display impls
pub mod format;
// Ensure constraint items are correctly re-exported or used via crate::constraint::
pub mod constraint;


use std::{
    collections::hash_map::DefaultHasher,
    fmt,
    hash::{Hash, Hasher},
    io::{self, BufWriter, Write as IOWrite},
    process::{Command, Stdio},
    str::FromStr,
    marker::PhantomData,
};

// Re-export necessary items from constraint
pub use constraint::{
    BinOp, BinRel, Bind, Constant, Constraint, DataCtor, DataDecl, DataField, Expr, Pred,
    Qualifier, Sort, SortCtor,
};
use derive_where::derive_where;
#[cfg(feature = "nightly")]
use rustc_macros::{Decodable, Encodable};
use serde::{
    de::{self, Deserializer, Visitor, MapAccess, SeqAccess},
    ser::SerializeTuple,
    Deserialize, Serialize,
};


// Added Debug to Self and all associated types.
// Added Serialize to Decimal & String. Added Clone to Var.
pub trait Types: fmt::Debug + Sized {
    type Sort: Identifier + Hash + Clone + for<'de> Deserialize<'de> + fmt::Debug + Serialize;
    type KVar: Identifier + Hash + Clone + for<'de> Deserialize<'de> + fmt::Debug + Serialize;
    type Var: Identifier + Hash + Clone + for<'de> Deserialize<'de> + fmt::Debug + Serialize;
    type Decimal: FixpointFmt + Hash + Clone + for<'de> Deserialize<'de> + fmt::Debug + Serialize;
    type String: FixpointFmt + Hash + Clone + for<'de> Deserialize<'de> + fmt::Debug + Serialize;
    type Tag: fmt::Display + FromStr + Hash + Clone + fmt::Debug + Serialize + for<'de> Deserialize<'de>;
}

pub trait FixpointFmt: Sized + fmt::Debug { // Added Debug
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
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

pub trait Identifier: Sized + fmt::Debug { // Added Debug
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
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

#[derive(Debug, Clone)] // Added Clone, DefaultTypes needs to be Clone if Types requires it implicitly
pub struct DefaultTypes;

// DefaultTypes now uses String to be DeserializeOwned and satisfy Debug/Serialize easily.
impl Types for DefaultTypes {
    type Sort = String;
    type KVar = String;
    type Var = String;
    type Tag = String;
    type Decimal = u32;
    type String = String;
}

impl Identifier for String {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl FixpointFmt for u32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
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
        type Decimal = $real:ty;
        type String = $str:ty;
        type Tag = $tag:ty;
    ) => {
        #[derive(Debug, Clone)] // Add Debug and Clone for the generated struct
        pub struct FixpointTypes; // Made pub
        pub mod fixpoint_generated { // Keep this mod for namespacing
            // Use crate::FixpointTypes for the outer struct
            // pub struct FixpointTypes; // This was shadowing
            pub type Expr = $crate::Expr<super::FixpointTypes>;
            pub type Pred = $crate::Pred<super::FixpointTypes>;
            pub type Constraint = $crate::Constraint<super::FixpointTypes>;
            pub type KVarDecl = $crate::KVarDecl<super::FixpointTypes>;
            pub type ConstDecl = $crate::ConstDecl<super::FixpointTypes>;
            pub type FunDef = $crate::FunDef<super::FixpointTypes>;
            pub type Task = $crate::Task<super::FixpointTypes>;
            pub type Qualifier = $crate::Qualifier<super::FixpointTypes>;
            pub type Sort = $crate::Sort<super::FixpointTypes>;
            pub type SortCtor = $crate::SortCtor<super::FixpointTypes>;
            pub type DataDecl = $crate::DataDecl<super::FixpointTypes>;
            pub type DataCtor = $crate::DataCtor<super::FixpointTypes>;
            pub type DataField = $crate::DataField<super::FixpointTypes>;
            pub type Bind = $crate::Bind<super::FixpointTypes>;
            pub type Constant = $crate::Constant<super::FixpointTypes>;
            pub use $crate::{BinOp, BinRel, ThyFunc};
        }

        impl $crate::Types for FixpointTypes {
            type Sort = $sort;
            type KVar = $kvar;
            type Var = $var;
            type Decimal = $real;
            type String = $str;
            type Tag = $tag;
        }
    };
}

#[derive_where(Hash, Debug, Clone)] // Added Debug, Clone
pub struct ConstDecl<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
    #[derive_where(skip)]
    pub comment: Option<String>,
}

#[derive_where(Hash, Debug, Clone)] // Added Debug, Clone
pub struct FunDef<T: Types> {
    pub name: T::Var,
    pub args: Vec<(T::Var, Sort<T>)>,
    pub out: Sort<T>,
    pub body: Expr<T>,
    #[derive_where(skip)]
    pub comment: Option<String>,
}

#[derive_where(Hash, Clone)] // Added Debug, Clone
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

#[derive(Clone, Copy, Hash, Debug, Serialize, Deserialize)] // Added Debug, Serialize, Deserialize
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

#[derive(Debug, Clone)]
pub struct Error<T: Types> {
    pub id: i32,
    pub tag: T::Tag,
    pub counterexample: Vec<(String, Expr<T>)>,
}

impl<T: Types> Serialize for Error<T>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut tuple = serializer.serialize_tuple(3)?;
        tuple.serialize_element(&self.id)?;
        tuple.serialize_element(&self.tag.to_string())?; // Assuming T::Tag -> String for this part is fine.
        // TODO: serialize this
        // tuple.serialize_element(&self.counterexample)?;
        tuple.end()
    }
}

impl<'de, T: Types> Deserialize<'de> for Error<T>
// Removed specific T::Var etc bounds as they are covered by T: Types
// and Expr<T>: Deserialize implicitly requires them via its own visitor logic.
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ErrorVisitor<T: Types>(PhantomData<T>);

        impl<'de, T: Types> Visitor<'de> for ErrorVisitor<T>
        {
            type Value = Error<T>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a 3-element array [id, tag_string, counterexample_list]")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let id: i32 = seq.next_element()?
                    .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                let tag_str: String = seq.next_element()?
                    .ok_or_else(|| de::Error::invalid_length(1, &self))?;
                let counterexample: Vec<(String, Expr<T>)> = seq.next_element()?
                    .ok_or_else(|| de::Error::invalid_length(2, &self))?;

                let tag = T::Tag::from_str(&tag_str)
                    .map_err(|_| de::Error::invalid_value(de::Unexpected::Str(&tag_str), &"a valid tag string"))?;

                Ok(Error { id, tag, counterexample })
            }
        }
        deserializer.deserialize_tuple(3, ErrorVisitor(PhantomData))
    }
}


#[derive(Serialize, Debug, Clone)]
#[serde(
    tag = "tag",
    content = "contents",
    bound(
        serialize = "T: Types", // Simplified: Serialize on T and its components will be checked by compiler
        deserialize = "T: Types" // Simplified: Deserialize on T and its components
    )
)]
pub enum FixpointResult<T: Types> {
    Safe(Stats),
    Unsafe(Stats, Vec<Error<T>>),
    Crash(CrashInfo),
}

impl<'de, T: Types> Deserialize<'de> for FixpointResult<T>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(field_identifier, rename_all = "lowercase")]
        enum Field { Tag, Contents }

        struct FixpointResultVisitor<T: Types>(PhantomData<T>);

        impl<'de, T: Types> Visitor<'de> for FixpointResultVisitor<T>
        {
            type Value = FixpointResult<T>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct FixpointResult")
            }

            fn visit_map<V>(self, mut map: V) -> Result<FixpointResult<T>, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut tag_opt: Option<String> = None;
                let mut contents_value_opt: Option<serde_json::Value> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Tag => {
                            if tag_opt.is_some() {
                                return Err(de::Error::duplicate_field("tag"));
                            }
                            tag_opt = Some(map.next_value()?);
                        }
                        Field::Contents => {
                            if contents_value_opt.is_some() {
                                return Err(de::Error::duplicate_field("contents"));
                            }
                            contents_value_opt = Some(map.next_value()?);
                        }
                    }
                }

                let tag_str = tag_opt.ok_or_else(|| de::Error::missing_field("tag"))?;
                let contents_value = contents_value_opt.ok_or_else(|| de::Error::missing_field("contents"))?;

                match tag_str.as_str() {
                    "Safe" => {
                        let safe_stats: Stats = serde_json::from_value(contents_value)
                            .map_err(de::Error::custom)?;
                        Ok(FixpointResult::Safe(safe_stats))
                    }
                    "Unsafe" => {
                        let (stats, errors_vec): (Stats, Vec<Error<T>>) = serde_json::from_value(contents_value)
                            .map_err(de::Error::custom)?;
                        Ok(FixpointResult::Unsafe(stats, errors_vec))
                    }
                    "Crash" => {
                        let crash_info: CrashInfo = serde_json::from_value(contents_value)
                            .map_err(de::Error::custom)?;
                        Ok(FixpointResult::Crash(crash_info))
                    }
                    other_tag => Err(de::Error::unknown_variant(other_tag, &["Safe", "Unsafe", "Crash"])),
                }
            }
        }
        deserializer.deserialize_map(FixpointResultVisitor(PhantomData))
    }
}


#[derive(Debug, Serialize, Deserialize, Default, Clone)]
#[serde(rename_all = "camelCase")]
pub struct Stats {
    pub num_cstr: i32,
    pub num_iter: i32,
    pub num_chck: i32,
    pub num_vald: i32,
    #[serde(default)]
    pub num_brkt: i32,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct CrashInfo(Vec<serde_json::Value>);

#[derive_where(Hash, Debug, Clone)] // Added Debug, Clone
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

    pub fn run(&self) -> io::Result<FixpointResult<T>> {
        let mut child = Command::new("fixpoint")
            .arg("-q")
            .arg("--stdin")
            .arg("--json")
            .arg("--allowho")
            .arg("--allowhoqs")
            .arg(format!("--solver={}", self.solver))
            .arg("--modelcounterexamples")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        let mut stdin = None;
        std::mem::swap(&mut stdin, &mut child.stdin);
        if let Some(stdin_pipe) = stdin {
            let mut w = BufWriter::new(stdin_pipe);
            writeln!(w, "{self}")?; // Task<T> needs fmt::Display
        } else {
            return Err(io::Error::new(io::ErrorKind::Other, "Failed to get stdin pipe for fixpoint"));
        }

        let out = child.wait_with_output()?;

        serde_json::from_slice(&out.stdout).map_err(|err| {
            eprintln!("Failed to parse fixpoint output: {}", err);
            eprintln!("Fixpoint stdout: {}", String::from_utf8_lossy(&out.stdout));
            eprintln!("Fixpoint stderr: {}", String::from_utf8_lossy(&out.stderr));
            if !out.stderr.is_empty() {
                let stderr = std::str::from_utf8(&out.stderr)
                    .unwrap_or("fixpoint exited with a non-zero return code");
                io::Error::new(io::ErrorKind::Other, stderr)
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


#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "nightly", derive(Encodable, Decodable))]
pub enum ThyFunc {
    StrLen, BvZeroExtend(u8), BvSignExtend(u8), IntToBv32, Bv32ToInt, IntToBv64, Bv64ToInt, BvUle, BvSle, BvUge, BvSge, BvUdiv, BvSdiv, BvSrem, BvUrem, BvLshr, BvAshr, BvAnd, BvOr, BvXor, BvNot, BvAdd, BvNeg, BvSub, BvMul, BvShl, BvUgt, BvSgt, BvUlt, BvSlt, SetEmpty, SetSng, SetCup, SetMem, MapDefault, MapSelect, MapStore,
}

impl ThyFunc {
    pub const ALL: [ThyFunc; 35] = [
        ThyFunc::StrLen, ThyFunc::IntToBv32, ThyFunc::Bv32ToInt, ThyFunc::IntToBv64, ThyFunc::Bv64ToInt, ThyFunc::BvAdd, ThyFunc::BvNeg, ThyFunc::BvSub, ThyFunc::BvShl, ThyFunc::BvLshr, ThyFunc::BvAshr, ThyFunc::BvMul, ThyFunc::BvUdiv, ThyFunc::BvSdiv, ThyFunc::BvUrem, ThyFunc::BvSrem, ThyFunc::BvAnd, ThyFunc::BvOr, ThyFunc::BvXor, ThyFunc::BvNot, ThyFunc::BvUle, ThyFunc::BvSle, ThyFunc::BvUge, ThyFunc::BvSge, ThyFunc::BvUgt, ThyFunc::BvSgt, ThyFunc::BvUlt, ThyFunc::BvSlt, ThyFunc::SetEmpty, ThyFunc::SetSng, ThyFunc::SetCup, ThyFunc::SetMem, ThyFunc::MapDefault, ThyFunc::MapSelect, ThyFunc::MapStore,
    ];
}

impl fmt::Display for ThyFunc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ThyFunc::StrLen => write!(f, "strLen"),
            ThyFunc::BvZeroExtend(size) => write!(f, "app (_ zero_extend {size})"),
            ThyFunc::BvSignExtend(size) => write!(f, "app (_ sign_extend {size})"),
            ThyFunc::IntToBv32 => write!(f, "int_to_bv32"),
            ThyFunc::Bv32ToInt => write!(f, "bv32_to_int"),
            ThyFunc::IntToBv64 => write!(f, "int_to_bv64"),
            ThyFunc::Bv64ToInt => write!(f, "bv64_to_int"),
            ThyFunc::BvUle => write!(f, "bvule"), ThyFunc::BvSle => write!(f, "bvsle"),
            ThyFunc::BvUge => write!(f, "bvuge"), ThyFunc::BvSge => write!(f, "bvsge"),
            ThyFunc::BvUdiv => write!(f, "bvudiv"), ThyFunc::BvSdiv => write!(f, "bvsdiv"),
            ThyFunc::BvUrem => write!(f, "bvurem"), ThyFunc::BvSrem => write!(f, "bvsrem"),
            ThyFunc::BvLshr => write!(f, "bvlshr"), ThyFunc::BvAshr => write!(f, "bvashr"),
            ThyFunc::BvAnd => write!(f, "bvand"), ThyFunc::BvOr => write!(f, "bvor"),
            ThyFunc::BvXor => write!(f, "bvxor"), ThyFunc::BvNot => write!(f, "bvnot"),
            ThyFunc::BvAdd => write!(f, "bvadd"), ThyFunc::BvNeg => write!(f, "bvneg"),
            ThyFunc::BvSub => write!(f, "bvsub"), ThyFunc::BvMul => write!(f, "bvmul"),
            ThyFunc::BvShl => write!(f, "bvshl"), ThyFunc::BvUgt => write!(f, "bvugt"),
            ThyFunc::BvSgt => write!(f, "bvsgt"), ThyFunc::BvUlt => write!(f, "bvult"),
            ThyFunc::BvSlt => write!(f, "bvslt"), ThyFunc::SetEmpty => write!(f, "Set_empty"),
            ThyFunc::SetSng => write!(f, "Set_sng"), ThyFunc::SetCup => write!(f, "Set_cup"),
            ThyFunc::SetMem => write!(f, "Set_mem"), ThyFunc::MapDefault => write!(f, "Map_default"),
            ThyFunc::MapSelect => write!(f, "Map_select"), ThyFunc::MapStore => write!(f, "Map_store"),
        }
    }
}
