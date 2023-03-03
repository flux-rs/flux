#![feature(rustc_private, min_specialization, once_cell, box_patterns, let_chains)]

extern crate rustc_index;
extern crate rustc_macros;
extern crate rustc_serialize;
extern crate rustc_span;

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
    BinOp, Const, ConstName, Constant, Constraint, Expr, Func, FuncSort, KVid, Name, Pred, Proj,
    Qualifier, Sign, Sort, UnOp,
};
use flux_common::{cache::QueryCache, format::PadAdapter};
use flux_config as config;
use itertools::Itertools;
use serde::{de, Deserialize};

use crate::constraint::DEFAULT_QUALIFIERS;

#[derive(Clone, Debug, Hash)]
pub struct ConstInfo {
    pub name: ConstName,
    pub orig: rustc_span::Symbol,
    pub sort: Sort,
}

pub struct Task<Tag> {
    pub comments: Vec<String>,
    pub constants: Vec<ConstInfo>,
    pub kvars: Vec<KVar>,
    pub constraint: Constraint<Tag>,
    pub qualifiers: Vec<Qualifier>,
    pub sorts: Vec<String>,
}

impl<Tag> Hash for Task<Tag> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.constants.hash(state);
        self.kvars.hash(state);
        self.constraint.hash(state);
        self.qualifiers.hash(state);
        self.sorts.hash(state);
    }
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

#[derive(Deserialize, Debug)]
pub struct CrashInfo(Vec<serde_json::Value>);

#[derive(Debug, Hash)]
pub struct KVar {
    kvid: KVid,
    sorts: Vec<Sort>,
    comment: String,
}

impl<Tag: fmt::Display + FromStr> Task<Tag> {
    pub fn new(
        comments: Vec<String>,
        constants: Vec<ConstInfo>,
        kvars: Vec<KVar>,
        constraint: Constraint<Tag>,
        qualifiers: Vec<Qualifier>,
        sorts: Vec<String>,
    ) -> Self {
        Task { comments, constants, kvars, constraint, qualifiers, sorts }
    }

    pub fn hash_with_default(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    pub fn check_with_cache(
        &self,
        key: String,
        cache: &mut QueryCache,
    ) -> io::Result<FixpointResult<Tag>> {
        let hash = self.hash_with_default();

        if config::is_cache_enabled() && cache.is_safe(&key, hash) {
            return Ok(FixpointResult::Safe(Default::default()));
        }

        let result = self.check();

        if config::is_cache_enabled() && let Ok(FixpointResult::Safe(_)) = result {
            cache.insert(key, hash);
        }
        result
    }

    fn check(&self) -> io::Result<FixpointResult<Tag>> {
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
            writeln!(w, "{self}")?;
        }
        let out = child.wait_with_output()?;

        let result = serde_json::from_slice(&out.stdout)?;

        Ok(result)
    }
}

impl KVar {
    pub fn new(kvid: KVid, sorts: Vec<Sort>, comment: String) -> Self {
        Self { kvid, sorts, comment }
    }
}

impl<Tag: fmt::Display> fmt::Display for Task<Tag> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for line in &self.comments {
            writeln!(f, "// {line}")?;
        }
        writeln!(f)?;

        for qualif in DEFAULT_QUALIFIERS.iter() {
            writeln!(f, "{qualif}")?;
        }

        for qualif in &self.qualifiers {
            writeln!(f, "{qualif}")?;
        }

        writeln!(f, "(data Pair 2 = [| Pair {{ fst: @(0), snd: @(1) }} ])")?;
        writeln!(f, "(data Unit 0 = [| Unit {{ }}])")?;

        for cinfo in &self.constants {
            writeln!(f, "{cinfo}")?;
        }

        for kvar in &self.kvars {
            writeln!(f, "{kvar}")?;
        }

        writeln!(f)?;
        write!(f, "(constraint")?;
        write!(PadAdapter::wrap_fmt(f, 2), "\n{}", self.constraint)?;
        writeln!(f, "\n)")
    }
}

impl fmt::Display for KVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(var {:?} ({})) // {}",
            self.kvid,
            self.sorts
                .iter()
                .format_with(" ", |sort, f| f(&format_args!("({sort})"))),
            self.comment
        )
    }
}

impl fmt::Display for ConstInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(constant {:?} {:?}) // orig: {}", self.name, self.sort, self.orig)
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
