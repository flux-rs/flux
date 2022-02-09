#![feature(rustc_private, min_specialization)]

extern crate rustc_serialize;

mod constraint;

use std::{
    fmt::{self, Write as FmtWrite},
    io::{self, BufWriter, Write as IOWrite},
    process::{Command, Stdio},
    str::FromStr,
};

pub use constraint::{BinOp, Constant, Constraint, Expr, KVid, Name, Pred, Sort, UnOp};
use itertools::Itertools;
use liquid_rust_common::format::PadAdapter;
use serde::{de, Deserialize};

pub struct Task<Tag> {
    pub kvars: Vec<KVar>,
    pub constraint: Constraint<Tag>,
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

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Stats {
    pub num_cstr: i32,
    pub num_iter: i32,
    pub num_chck: i32,
    pub num_vald: i32,
}

#[derive(Deserialize, Debug)]
pub struct CrashInfo(Vec<serde_json::Value>);

#[derive(Debug)]
pub struct KVar(pub KVid, pub Vec<Sort>);

impl<Tag: fmt::Display + FromStr> Task<Tag> {
    pub fn new(kvars: Vec<KVar>, constraint: Constraint<Tag>) -> Self {
        Task { kvars, constraint }
    }

    pub fn check(&self) -> io::Result<FixpointResult<Tag>> {
        let mut child = Command::new("fixpoint")
            .arg("-q")
            .arg("--stdin")
            .arg("--json")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .unwrap();
        let mut stdin = None;
        std::mem::swap(&mut stdin, &mut child.stdin);
        {
            let mut w = BufWriter::new(stdin.unwrap());
            // let mut w = BufWriter::new(std::io::stdout());

            writeln!(w, "{}", self)?;
        }
        let out = child.wait_with_output()?;

        let result = serde_json::from_slice(&out.stdout)?;

        Ok(result)
    }
}

impl<Tag: fmt::Display> fmt::Display for Task<Tag> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Unary
        writeln!(f, "(qualif EqZero ((v int)) (v == 0))")?;
        writeln!(f, "(qualif GtZero ((v int)) (v > 0))")?;
        writeln!(f, "(qualif GeZero ((v int)) (v >= 0))")?;
        writeln!(f, "(qualif LtZero ((v int)) (v < 0))")?;
        writeln!(f, "(qualif LeZero ((v int)) (v <= 0))")?;

        // Binary
        writeln!(f, "(qualif Eq ((a int) (b int)) (a == b))")?;
        writeln!(f, "(qualif Gt ((a int) (b int)) (a > b))")?;
        writeln!(f, "(qualif Lt ((a int) (b int)) (a < b))")?;
        writeln!(f, "(qualif Ge ((a int) (b int)) (a >= b))")?;
        writeln!(f, "(qualif Le ((a int) (b int)) (a <= b))")?;
        writeln!(f, "(qualif Le1 ((a int) (b int)) (a < b - 1))")?;
        // writeln!(f, "(qualif Foo ((a int) (b int)) (a <= b/2))")?;

        for kvar in &self.kvars {
            writeln!(f, "{}", kvar)?;
        }
        writeln!(f)?;
        write!(f, "(constraint")?;
        write!(PadAdapter::wrap_fmt(f), "\n{}", self.constraint)?;
        writeln!(f, "\n)")
    }
}

impl fmt::Display for KVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(var {:?} ({}))",
            self.0,
            self.1
                .iter()
                .format_with(" ", |sort, f| f(&format_args!("({})", sort)))
        )
    }
}

impl<Tag: fmt::Display> fmt::Debug for Task<Tag> {
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
