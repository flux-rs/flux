use super::*;
use serde::Deserialize;
use std::{
    io::{self, BufWriter, Write},
    process::{Command, Stdio},
};

#[derive(Deserialize, Debug)]
pub struct LiquidResult {
    pub tag: Safeness,
}

#[derive(Deserialize, Eq, PartialEq, Debug)]
pub enum Safeness {
    Safe,
    Unsafe,
}

pub fn solve(constraint: &Constraint) -> io::Result<LiquidResult> {
    let mut kid = Command::new("fixpoint")
        .arg("-q")
        .arg("--stdin")
        .arg("--json")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()?;

    let mut stdin = None;
    std::mem::swap(&mut stdin, &mut kid.stdin);
    {
        let mut w = BufWriter::new(stdin.unwrap());
        // let mut w = BufWriter::new(io::stdout());
        emit_preamble(&mut w)?;
        emit_kvars(&mut w, constraint)?;
        write!(w, "(constraint")?;
        constraint.emit(&mut w, 2)?;
        write!(w, ")")?;
    }

    let out = kid.wait_with_output()?;
    let result = serde_json::from_slice(&out.stdout)?;

    Ok(result)
}

fn emit_kvars<W: Write>(w: &mut W, c: &Constraint) -> io::Result<()> {
    for (kvid, sorts) in KvarInferer::new().infer(c) {
        write!(w, "(var $k{} (", kvid)?;
        for i in 0..sorts.len() {
            if i > 0 {
                write!(w, " ")?;
            }
            write!(w, "({})", sorts[i])?;
        }
        write!(w, "))\n")?;
    }
    Ok(())
}

fn emit_preamble<W: Write>(w: &mut W) -> io::Result<()> {
    write!(
        w,
        "(qualif Eq ((x int) (y int)) (x = y))
(qualif Ge ((x int) (y int)) (x >= y))
(qualif Gt ((x int) (y int)) (x > y))
(qualif GeZero ((x int)) (x >= 0))
(qualif GtZero ((x int)) (x > 0))

(data Unit 0 = [
    | Unit {{ }}
])

"
    )
}

macro_rules! indent {
    ($writer:expr, $indent:expr) => {
        ::std::write!($writer, "\n{:>1$}", "", $indent)
    };
}

impl Constraint {
    fn emit<W: Write>(&self, w: &mut W, indent: usize) -> io::Result<()> {
        match self {
            Constraint::True => {
                indent!(w, indent)?;
                write!(w, "((true))")?;
            }
            Constraint::Pred(pred) => {
                indent!(w, indent)?;
                write!(w, "(")?;
                pred.emit(w)?;
                write!(w, ")")?;
            }
            Constraint::Conj(constraints) => match constraints.len() {
                0 => {
                    indent!(w, indent)?;
                    write!(w, "((true))")?
                }
                1 => constraints[0].emit(w, indent)?,
                _ => {
                    indent!(w, indent)?;
                    write!(w, "(and")?;
                    for c in constraints {
                        c.emit(w, indent + 2)?;
                    }
                    write!(w, ")")?;
                }
            },
            Constraint::Forall(var, sort, pred, body) => {
                indent!(w, indent)?;
                write!(w, "(forall (({} {}) ", var, sort)?;
                pred.emit(w)?;
                write!(w, ")")?;
                body.emit(w, indent + 2)?;
                write!(w, ")")?;
            }
            Constraint::Guard(guard, body) => {
                indent!(w, indent)?;
                write!(w, "(forall ((_ int) ")?;
                guard.emit(w)?;
                write!(w, ")")?;
                body.emit(w, indent + 2)?;
                write!(w, ")")?;
            }
        }
        Ok(())
    }
}

impl Pred {
    fn emit<W: Write>(&self, w: &mut W) -> io::Result<()> {
        match self {
            Pred::Kvar(kvar) => {
                write!(w, "($k{}", kvar.0)?;
                for var in &kvar.1 {
                    write!(w, " {}", var)?;
                }
                write!(w, ")")?;
            }
            Pred::Conj(preds) => {
                write!(w, "(and")?;
                for pred in preds {
                    write!(w, " ")?;
                    pred.emit(w)?;
                }
                write!(w, ")")?;
            }
            Pred::Expr(expr) => {
                write!(w, "(")?;
                expr.emit(w)?;
                write!(w, ")")?;
            }
            Pred::True => {
                write!(w, "((true))")?;
            }
        }
        Ok(())
    }
}

impl Expr {
    fn emit<W: Write>(&self, w: &mut W) -> io::Result<()> {
        match self {
            Expr::Var(var) => {
                write!(w, "{}", var)?;
            }
            Expr::Constant(Constant::Unit) => {
                write!(w, "Unit")?;
            }
            Expr::Constant(c) => {
                write!(w, "{}", c)?;
            }
            Expr::BinaryOp(bin_op, op1, op2) => {
                write!(w, "(")?;
                op1.emit(w)?;
                write!(w, " {} ", bin_op)?;
                op2.emit(w)?;
                write!(w, ")")?;
            }
            Expr::UnaryOp(un_op, op) => match un_op {
                UnOp::Not => {
                    write!(w, "(not ")?;
                    op.emit(w)?;
                    write!(w, ")")?;
                }
            },
        }
        Ok(())
    }
}
