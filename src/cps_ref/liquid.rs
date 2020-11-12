use super::{
    ast,
    constraint::{self, Constraint, PredC},
    utils::Dict,
    utils::Scoped,
};
use serde;
use std::{
    collections::HashMap,
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

enum Sort {
    Bool,
    Int,
}

impl std::fmt::Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::Bool => write!(f, "bool"),
            Sort::Int => write!(f, "int"),
        }
    }
}

#[derive(serde::Deserialize)]
struct LiquidResult {
    result: Safeness,
}

pub struct LiquidSolver<'a> {
    buf: BufWriter<ChildStdin>,
    kid: Child,
    map: Scoped<HashMap<ast::Var, &'a constraint::Sort>>,
}

impl<'a> LiquidSolver<'a> {
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
            map: Scoped::default(),
            kid,
        })
    }

    pub fn check(
        mut self,
        c: &'a Constraint,
        kvars: &[(u32, Vec<constraint::Sort>)],
    ) -> io::Result<bool> {
        self.write_qualifs()?;
        self.write_kvars(kvars)?;
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

    fn write_kvars(&mut self, kvars: &[(u32, Vec<constraint::Sort>)]) -> io::Result<()> {
        for &(n, ref sorts) in kvars {
            let mut v = vec![];
            sorts
                .iter()
                .for_each(|s| s.flatten(|(sort, _)| v.push(format!("({})", sort))));
            write!(self.buf, "\n(var $k{} ({}))", n, v.join(" "))?;
        }
        Ok(())
    }

    fn write_constraint(&mut self, c: &'a Constraint) -> io::Result<()> {
        write!(self.buf, "\n(constraint")?;
        self.map.push(HashMap::default());
        self.write_constraint_rec(c, 2)?;
        write!(self.buf, ")")?;
        Ok(())
    }

    fn write_constraint_rec(&mut self, c: &'a Constraint, mut indent: usize) -> io::Result<()> {
        match c {
            Constraint::Pred(p) => {
                write!(self.buf, "\n{:>1$}((", "", indent + 2)?;
                self.write_pred(p)?;
                write!(self.buf, "))")?;
            }
            Constraint::Conj(cs) => match cs.len() {
                0 => write!(self.buf, "\n{:>1$}((true))", "", indent)?,
                1 => self.write_constraint_rec(&cs[0], indent)?,
                _ => {
                    write!(self.buf, "\n{:>1$}(and", "", indent)?;
                    for c in cs {
                        self.map.push(HashMap::new());
                        self.write_constraint_rec(c, indent + 2)?;
                        self.map.pop();
                    }
                    write!(self.buf, ")")?;
                }
            },
            &Constraint::Forall {
                bind,
                ref sort,
                ref hyp,
                ref body,
            } => {
                let mut bindings = vec![];
                sort.flatten(|(sort, proj)| bindings.push((place_to_string(bind, proj), sort)));
                let mut n = 1;
                if bindings.is_empty() {
                    write!(self.buf, "\n{:>1$}(forall ((_ int) (true))", "", indent)?;
                } else {
                    for i in 0..bindings.len() - 1 {
                        let (x, sort) = &bindings[i];
                        write!(
                            self.buf,
                            "\n{:>3$}(forall (({} {}) (true))",
                            "", x, sort, indent
                        )?;
                        indent += 2;
                        n += 1;
                    }
                    let (x, sort2) = bindings.last().unwrap();
                    write!(self.buf, "\n{:>3$}(forall (({} {}) (", "", x, sort2, indent)?;
                    self.write_pred(hyp)?;

                    self.map.insert(bind, sort);
                    write!(self.buf, "))")?;
                }
                self.write_constraint_rec(body, indent + 2)?;
                write!(self.buf, "{:)>1$}", ")", n)?;
            }
            Constraint::Guard(p, c) => {
                write!(self.buf, "\n{:>1$}(forall ((_ int) (", "", indent)?;
                self.write_pred(p)?;
                write!(self.buf, "))")?;
                self.write_constraint_rec(c, indent + 2)?;
                write!(self.buf, ")")?;
            }
            Constraint::True => write!(self.buf, "\n{:>1$}((true))", "", indent)?,
            Constraint::Err => bug!(),
        }
        Ok(())
    }

    fn write_pred(&mut self, p: &PredC) -> io::Result<()> {
        match p {
            PredC::Place(constraint::Place { var, proj }) => {
                write!(self.buf, "{}", place_to_string(*var, proj.iter()))?;
            }
            &PredC::Constant(c) => match c {
                ast::ConstantP::Bool(b) => {
                    write!(self.buf, "{}", if b { "true" } else { "false" })?
                }
                ast::ConstantP::Int(n) => write!(self.buf, "{}", n)?,
            },
            PredC::BinaryOp(op, lhs, rhs) => {
                write!(self.buf, "(")?;
                self.write_pred(lhs)?;
                write!(self.buf, " {:?} ", op)?;
                self.write_pred(rhs)?;
                write!(self.buf, ")")?;
            }
            PredC::UnaryOp(op, operand) => match op {
                ast::UnOp::Not => {
                    write!(self.buf, "(not ")?;
                    self.write_pred(operand)?;
                    write!(self.buf, ")")?;
                }
            },
            PredC::Iff(lhs, rhs) => {
                write!(self.buf, "(")?;
                self.write_pred(lhs)?;
                write!(self.buf, " <=> ")?;
                self.write_pred(rhs)?;
                write!(self.buf, ")")?;
            }
            PredC::Kvar(n, places) => {
                write!(self.buf, "$k{} ", n)?;
                let mut expanded = vec![];
                for p in places {
                    if let Some(sort) = self.map.get(&p.var) {
                        sort.flatten(|(_, proj)| {
                            expanded.push(place_to_string(p.var, p.proj.iter().chain(proj)));
                        });
                    } else {
                        expanded.push(place_to_string(p.var, p.proj.iter()));
                    }
                }
                write!(self.buf, "{}", expanded.join(" "))?;
            }
            PredC::Conj(preds) => {
                write!(self.buf, "and")?;
                for p in preds {
                    write!(self.buf, " (")?;
                    self.write_pred(p)?;
                    write!(self.buf, ")")?;
                }
            }
        }
        Ok(())
    }
}

fn place_to_string<'a, I>(var: ast::Var, projection: I) -> String
where
    I: IntoIterator<Item = &'a u32>,
{
    let mut s = format!("{:?}", var);
    for p in projection {
        s.push_str(&format!(".{}", p));
    }
    s
}

impl constraint::Sort {
    fn flatten(&self, mut act: impl for<'a> FnMut((Sort, &'a Vec<u32>))) {
        self.flatten_rec(&mut act, &mut vec![]);
    }

    fn flatten_rec(&self, act: &mut impl for<'a> FnMut((Sort, &'a Vec<u32>)), proj: &mut Vec<u32>) {
        match self {
            constraint::Sort::Int => act((Sort::Int, proj)),
            constraint::Sort::Bool => act((Sort::Bool, proj)),
            constraint::Sort::Tuple(sorts) => {
                for (i, sort) in sorts.iter().enumerate() {
                    proj.push(i as u32);
                    sort.flatten_rec(act, proj);
                    proj.pop();
                }
            }
        }
    }
}
