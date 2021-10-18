#![feature(rustc_private, min_specialization)]

extern crate rustc_serialize;

mod constraint;

use std::{
    io::{self, BufWriter, Write},
    process::{Command, Stdio},
};

pub use constraint::{BinOp, Constant, Constraint, Expr, Pred, Sort, Var};
use liquid_rust_common::format::PadAdapter;
use serde::Deserialize;

pub struct Fixpoint;

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

impl Fixpoint {
    pub fn check(constraint: &Constraint) -> io::Result<FixpointResult> {
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

            // emit_preamble(&mut w).unwrap();

            writeln!(
                w,
                "(constraint \n{}\n)",
                PadAdapter::wrap_on_newline(constraint)
            )?;
        }
        let out = child.wait_with_output()?;

        let result = serde_json::from_slice(&out.stdout)?;

        Ok(result)
    }
}
