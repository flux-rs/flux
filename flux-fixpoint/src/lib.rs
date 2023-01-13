#![feature(rustc_private, min_specialization, once_cell, box_patterns, let_chains)]

extern crate rustc_index;
extern crate rustc_serialize;

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
    BinOp, Const, Constant, Constraint, Expr, Func, FuncSort, KVid, Name, Pred, Proj, Qualifier,
    Sign, Sort, UifDef, UnOp,
};
use flux_common::{cache::QueryCache, config, format::PadAdapter};
use itertools::Itertools;
use serde::{de, Deserialize};

use crate::constraint::DEFAULT_QUALIFIERS;

pub struct Task<Tag> {
    pub constants: Vec<(Name, Sort)>,
    pub kvars: Vec<KVar>,
    pub constraint: Constraint<Tag>,
    pub qualifiers: Vec<Qualifier>,
    pub uifs: Vec<UifDef>,
    pub sorts: Vec<String>,
}

impl<Tag> Hash for Task<Tag> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.constants.hash(state);
        self.kvars.hash(state);
        self.constraint.hash(state);
        self.qualifiers.hash(state);
        self.uifs.hash(state);
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
pub struct KVar(pub KVid, pub Vec<Sort>);

impl<Tag: fmt::Display + FromStr> Task<Tag> {
    pub fn new(
        constants: Vec<(Name, Sort)>,
        kvars: Vec<KVar>,
        constraint: Constraint<Tag>,
        qualifiers: Vec<Qualifier>,
        uifs: Vec<UifDef>,
        sorts: Vec<String>,
    ) -> Self {
        Task { constants, kvars, constraint, qualifiers, uifs, sorts }
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
            // let mut w = BufWriter::new(std::io::stdout());

            writeln!(w, "{self}")?;
        }
        let out = child.wait_with_output()?;

        let result = serde_json::from_slice(&out.stdout)?;

        Ok(result)
    }
}

impl<Tag: fmt::Display> fmt::Display for Task<Tag> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for qualif in DEFAULT_QUALIFIERS.iter() {
            writeln!(f, "{qualif}")?;
        }

        for qualif in &self.qualifiers {
            writeln!(f, "{qualif}")?;
        }

        writeln!(f, "(data Pair 2 = [| Pair {{ fst: @(0), snd: @(1) }} ])")?;
        writeln!(f, "(data Unit 0 = [| Unit {{ }}])")?;

        for (name, sort) in &self.constants {
            write!(f, "(constant {name:?} {sort:?})")?;
        }

        for uif_def in &self.uifs {
            writeln!(f, "{uif_def}")?;
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
            "(var {:?} ({}))",
            self.0,
            self.1
                .iter()
                .format_with(" ", |sort, f| f(&format_args!("({sort})")))
        )
    }
}

impl fmt::Display for UifDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(constant {} {})", self.name, self.sort)
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
