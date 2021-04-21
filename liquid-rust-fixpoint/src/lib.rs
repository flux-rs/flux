mod constraint;
use serde::Deserialize;
mod embed;
mod emit;

use std::{
    io::{BufWriter, Write},
    process::{Command, Stdio},
};

use constraint::{Expr, KVarGatherCtx, Qualifier, Sort};
use embed::Embed;
use emit::Emit;
use liquid_rust_lrir::ty::BaseTy;

use liquid_rust_lrir::{mir::BinOp, ty::Var};

pub use constraint::Constraint;

#[derive(Default)]
pub struct Fixpoint {
    scope: Vec<Var>,
}

impl Fixpoint {
    pub fn push_var(&mut self, var: Var) -> usize {
        let index = self.scope.len();
        self.scope.push(var);
        index
    }

    pub fn pop_var(&mut self) -> Var {
        self.scope.pop().unwrap()
    }

    fn get_index(&self, target: &Var) -> Option<usize> {
        for (index, var) in self.scope.iter().enumerate() {
            if var == target {
                return Some(index);
            }
        }
        None
    }

    pub fn embed<E: Embed>(&self, e: &E) -> E::Output {
        e.embed(self)
    }

    pub fn check(&self, constraint: Constraint) -> FixpointResult {
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
                BinOp::Eq(BaseTy::Bool),
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
