use super::{
    ast,
    constraint::{Constraint, PredC},
    utils::ScopedHashMap,
};
use ast::BasicType;
use std::{
    fs::{File, OpenOptions},
    io::{self, BufWriter, Write},
    path::Path,
    process::Command,
};

pub struct LiquidSolver {
    buf: BufWriter<File>,
}

impl LiquidSolver {
    pub fn new() -> io::Result<Self> {
        let path = Path::new("file.smt2");
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;
        let buf = BufWriter::with_capacity(1000, file);

        Ok(Self { buf })
    }

    pub fn check(mut self, c: &Constraint) -> io::Result<bool> {
        write!(
            self.buf,
            "
(qualif Eq ((x int) (y int)) (x = y))
(qualif Ge ((x int) (y int)) (x >= y))
(qualif Gt ((x int) (y int)) (x > y))
(qualif GeZero ((x int)) (x >= 0))
(qualif GtZero ((x int)) (x > 0))
"
        )?;
        self.write_kvars(c, &mut ScopedHashMap::new())?;
        write!(self.buf, "\n(constraint")?;
        self.write_constraint(c, 2)?;
        write!(self.buf, ")")?;
        self.buf.flush()?;
        let st = Command::new("fixpoint")
            .arg("file.smt2")
            // .stdout(Stdio::piped())
            // .stderr(Stdio::piped())
            .status()?;
        Ok(st.success())
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

    fn write_constraint(&mut self, c: &Constraint, indent: usize) -> io::Result<()> {
        match c {
            Constraint::Pred(p) => {
                write!(self.buf, "\n{:>1$}((", "", indent + 2)?;
                self.write_pred(p, &[])?;
                write!(self.buf, "))")?;
            }
            Constraint::Conj(cs) => match cs.len() {
                0 => write!(self.buf, "{:>1$}true", "", indent)?,
                1 => self.write_constraint(&cs[0], indent)?,
                _ => {
                    write!(self.buf, "\n{:>1$}(and", "", indent)?;
                    for c in cs {
                        self.write_constraint(c, indent + 2)?;
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
                self.write_constraint(body, indent + 2)?;
                write!(self.buf, ")")?;
            }
            Constraint::Guard(p, c) => {
                write!(self.buf, "\n{:>1$}(forall ((_ int) (", "", indent)?;
                self.write_pred(p, &[])?;
                write!(self.buf, "))")?;
                self.write_constraint(c, indent + 2)?;
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
