use super::{
    ast,
    constraint::{Constraint, PredC},
    utils::ScopedHashMap,
};
use ast::BasicType;
use serde;
use std::{
    io::{self, BufWriter, Write},
    process::{Child, ChildStdin, Command, Stdio},
};

#[derive(serde::Deserialize, Eq, PartialEq)]
enum Safeness {
    #[serde(rename(deserialize = "safe"))]
    Safe,
    #[serde(rename(deserialize = "unsafe"))]
    Unsafe,
}

#[derive(serde::Deserialize)]
struct LiquidResult {
    result: Safeness,
}

pub struct LiquidSolver {
    buf: BufWriter<ChildStdin>,
    kid: Child,
}

impl LiquidSolver {
    pub fn new() -> io::Result<Self> {
        let mut kid = Command::new("fixpoint")
            .arg("-q")
            .arg("--stdin")
            .arg("--json")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let mut stdin = None;
        ::std::mem::swap(&mut stdin, &mut kid.stdin);

        Ok(Self {
            buf: BufWriter::new(stdin.unwrap()),
            kid,
        })
    }

    pub fn check(mut self, c: &Constraint) -> io::Result<bool> {
        self.write_qualifs()?;
        self.write_kvars(c, &mut ScopedHashMap::new())?;
        self.write_constraint(c)?;

        // Close the pipe to reach EOF
        drop(self.buf);

        let out = self.kid.wait_with_output()?;
        let res: LiquidResult = serde_json::from_slice(&out.stdout)?;

        Ok(res.result == Safeness::Safe)
    }

    fn write_qualifs(&mut self) -> io::Result<()> {
        write!(
            self.buf,
            "
(qualif Eq ((x int) (y int)) (x = y))
(qualif Ge ((x int) (y int)) (x >= y))
(qualif Gt ((x int) (y int)) (x > y))
(qualif GeZero ((x int)) (x >= 0))
(qualif GtZero ((x int)) (x > 0))
"
        )
    }

    fn write_kvars(
        &mut self,
        c: &Constraint,
        tys: &mut ScopedHashMap<ast::Symbol, BasicType>,
    ) -> io::Result<()> {
        match c {
            Constraint::Conj(cs) => {
                for c in cs {
                    tys.enter_scope(|tys| self.write_kvars(c, tys))?;
                }
            }
            &Constraint::Forall {
                bind,
                ty,
                ref hyp,
                ref body,
            } => {
                tys.insert(bind, ty);
                match hyp {
                    PredC::Kvar(n, vars) => {
                        write!(self.buf, "(var $k{} (", n)?;
                        for v in vars {
                            write!(self.buf, " (")?;
                            self.write_ty(tys[v])?;
                            write!(self.buf, ")")?;
                        }
                        write!(self.buf, "))\n")?;
                    }
                    _ => {}
                }
                self.write_kvars(body, tys)?;
            }
            Constraint::Guard(_, p) => {
                self.write_kvars(p, tys)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn write_ty(&mut self, ty: BasicType) -> io::Result<()> {
        match ty {
            BasicType::Bool => write!(self.buf, "bool")?,
            BasicType::Int => write!(self.buf, "int")?,
        }
        Ok(())
    }

    fn write_constraint(&mut self, c: &Constraint) -> io::Result<()> {
        write!(self.buf, "\n(constraint")?;
        self.write_constraint_(c, 2)?;
        write!(self.buf, ")")?;
        Ok(())
    }

    fn write_constraint_(&mut self, c: &Constraint, indent: usize) -> io::Result<()> {
        match c {
            Constraint::Pred(p) => {
                write!(self.buf, "\n{:>1$}((", "", indent + 2)?;
                self.write_pred(p, &[])?;
                write!(self.buf, "))")?;
            }
            Constraint::Conj(cs) => match cs.len() {
                0 => write!(self.buf, "{:>1$}true", "", indent)?,
                1 => self.write_constraint_(&cs[0], indent)?,
                _ => {
                    write!(self.buf, "\n{:>1$}(and", "", indent)?;
                    for c in cs {
                        self.write_constraint_(c, indent + 2)?;
                    }
                    write!(self.buf, ")")?;
                }
            },
            &Constraint::Forall {
                bind,
                ty,
                ref hyp,
                ref body,
            } => {
                write!(self.buf, "\n{:>2$}(forall (({} ", "", bind, indent)?;
                self.write_ty(ty)?;
                write!(self.buf, ") (")?;
                self.write_pred(hyp, &[])?;
                write!(self.buf, "))")?;
                self.write_constraint_(body, indent + 2)?;
                write!(self.buf, ")")?;
            }
            Constraint::Guard(p, c) => {
                write!(self.buf, "\n{:>1$}(forall ((_ int) (", "", indent)?;
                self.write_pred(p, &[])?;
                write!(self.buf, "))")?;
                self.write_constraint_(c, indent + 2)?;
                write!(self.buf, ")")?;
            }
            Constraint::True => write!(self.buf, "{:>1$}true", "", indent)?,
            Constraint::Err => bug!(),
        }
        Ok(())
    }

    fn write_pred(&mut self, p: &PredC, vars: &[ast::Symbol]) -> io::Result<()> {
        match p {
            PredC::Var(v) => {
                write!(self.buf, "{}", &*v.as_str())?;
            }
            PredC::Constant(c) => {
                write!(self.buf, "{:?}", c)?;
            }
            PredC::BinaryOp(op, lhs, rhs) => {
                write!(self.buf, "(")?;
                self.write_pred(lhs, vars)?;
                write!(self.buf, " {:?} ", op)?;
                self.write_pred(rhs, vars)?;
                write!(self.buf, ")")?;
            }
            PredC::UnaryOp(op, operand) => match op {
                ast::UnOp::Not => {
                    write!(self.buf, "(not ")?;
                    self.write_pred(operand, vars)?;
                    write!(self.buf, ")")?;
                }
            },
            PredC::Iff(lhs, rhs) => {
                write!(self.buf, "(")?;
                self.write_pred(lhs, vars)?;
                write!(self.buf, " <=> ")?;
                self.write_pred(rhs, vars)?;
                write!(self.buf, ")")?;
            }
            PredC::Kvar(n, vars) => {
                write!(self.buf, "$k{}", n)?;
                for v in vars {
                    write!(self.buf, " {}", &*v.as_str())?;
                }
                // write!(self.buf, ")")?;
            }
        }
        Ok(())
    }
}
