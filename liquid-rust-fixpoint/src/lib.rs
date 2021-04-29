mod constraint;
use serde::Deserialize;
mod emit;

use std::{
    fs::{canonicalize, File},
    io::{BufWriter, Write},
    process::{Command, Stdio},
};

use constraint::{KVarGatherCtx, Qualifier};
use emit::Emit;

pub use constraint::{BinOp, Constant, Constraint, Expr, KVid, Pred, Sort, UnOp};

use liquid_rust_common::config::*;

#[derive(Default)]
pub struct Fixpoint;

impl Fixpoint {
    pub fn check(&self, constraint: Constraint) -> FixpointResult {
        // First dump the constraint to a file
        // for debug purposes
        if should_dump_constraint() {
            let p = canonicalize(dump_constraint()).expect("couldn't get path");
            let mut w = BufWriter::new(File::create(p).expect("couldn't create file to dump constraints"));

            emit_preamble(&mut w).unwrap();

            for kvar in KVarGatherCtx::gather_kvars(&constraint) {
                emit!(w, &0, "{}", kvar).unwrap();
            }

            emit!(w, &0, "(constraint {})", &constraint).unwrap();
        }
        
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

            emit_preamble(&mut w).unwrap();

            for kvar in KVarGatherCtx::gather_kvars(&constraint) {
                emit!(w, &0, "{}", kvar).unwrap();
            }

            emit!(w, &0, "(constraint {})", constraint).unwrap();
        }

        let out = child.wait_with_output().unwrap();

        serde_json::from_slice(&out.stdout).unwrap()
    }
}

fn emit_preamble<W: std::io::Write>(w: &mut W) -> std::io::Result<()> {
    let qualifiers = [
        Qualifier {
            name: "Eq".into(),
            vars: vec![Sort::Int, Sort::Int],
            pred: Expr::BinaryOp(
                BinOp::Eq,
                Box::new(Expr::Variable(0)),
                Box::new(Expr::Variable(1)),
            ),
        },
        Qualifier {
            name: "Lte".into(),
            vars: vec![Sort::Int, Sort::Int],
            pred: Expr::BinaryOp(
                BinOp::Lte,
                Box::new(Expr::Variable(0)),
                Box::new(Expr::Variable(1)),
            ),
        },
    ];
    for qualif in qualifiers.iter() {
        emit!(w, &0, "{}", qualif)?;
    }
    Ok(())
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
