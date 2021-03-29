mod constant;
mod constraint;
mod embed;
mod emit;
mod pred;
mod sort;

use std::{
    io::{BufWriter, Write},
    process::{Command, Stdio},
};

use embed::Embed;
use emit::Emit;

use liquid_rust_lrir::ty::Var;

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

    fn get_index(&self, target: &Var) -> usize {
        for (index, var) in self.scope.iter().enumerate() {
            if var == target {
                return index;
            }
        }
        panic!()
    }

    pub fn embed<E: Embed>(&self, e: &E) -> E::Output {
        e.embed(self)
    }

    pub fn check(&self, constraint: Constraint) {
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
            emit!(w, &0, "(constraint {})", constraint).unwrap();
        }

        let out = child.wait_with_output().unwrap();

        if !out.status.success() {
            panic!("{:?}", out);
        }
    }
}
