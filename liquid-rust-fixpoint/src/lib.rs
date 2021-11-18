#![feature(rustc_private, min_specialization)]

extern crate rustc_serialize;

mod constraint;

use std::{
    fmt::{self, Write as FmtWrite},
    io::{self, BufWriter, Write as IOWrite},
    process::{Command, Stdio},
};

pub use constraint::{BinOp, Constant, Constraint, Expr, KVid, Name, Pred, Sort, UnOp};
use itertools::Itertools;
use liquid_rust_common::format::PadAdapter;
use serde::Deserialize;

pub struct Fixpoint {
    pub kvars: Vec<KVar>,
    pub constraint: Constraint,
}

#[derive(Deserialize, Debug)]
pub struct FixpointResult {
    pub tag: Safeness,
}

#[derive(Deserialize, Eq, PartialEq, Debug)]
pub enum Safeness {
    Safe,
    Unsafe,
    Crash,
}

#[derive(Debug)]
pub struct KVar(pub KVid, pub Vec<Sort>);

impl Fixpoint {
    pub fn new(kvars: Vec<KVar>, constraint: Constraint) -> Self {
        Fixpoint { kvars, constraint }
    }

    pub fn check(&self) -> io::Result<FixpointResult> {
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

impl fmt::Display for Fixpoint {
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
        writeln!(f, "(qualif Ge ((a int) (b int)) (a >= b))")?;

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
