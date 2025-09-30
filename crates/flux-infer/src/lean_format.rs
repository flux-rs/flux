use core::fmt;

use itertools::Itertools;
use liquid_fixpoint::{FixpointFmt, Identifier};

use crate::{
    fixpoint_encoding::fixpoint::{
        BinOp, BinRel, ConstDecl, Constant, Constraint, Expr, FunDef, Pred, Sort, Var,
    },
    lean_encoding::{ConstDef, LeanEncoder},
};

struct LeanSort<'a>(&'a Sort);
struct LeanFunDef<'a>(&'a FunDef);
struct LeanConstDef<'a>(&'a ConstDef);
struct LeanConstraint<'a>(&'a Constraint);
struct LeanPred<'a>(&'a Pred);
struct LeanExpr<'a>(&'a Expr);
struct LeanVar<'a>(&'a Var);

impl<'a> fmt::Display for LeanVar<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.display().to_string().replace("$", "_"))
    }
}

impl<'a> fmt::Display for LeanConstDef<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let LeanConstDef(ConstDef(ConstDecl { name, sort, comment: _ }, def)) = self;
        if let Some(def) = def {
            write!(f, "def {} : {} := {}", LeanVar(name), LeanSort(sort), LeanExpr(def))
        } else {
            write!(f, "axiom {} : {}", LeanVar(name), LeanSort(sort))
        }
    }
}

impl<'a> fmt::Display for LeanSort<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Sort::Int => write!(f, "Int"),
            Sort::Bool => write!(f, "Bool"),
            Sort::Real => write!(f, "Real"),
            Sort::Str => write!(f, "String"),
            Sort::Func(f_sort) => {
                write!(f, "({} -> {})", LeanSort(&f_sort[0]), LeanSort(&f_sort[1]))
            }
            _ => todo!(),
        }
    }
}

impl<'a> fmt::Display for LeanExpr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Expr::Var(v) => write!(f, "{}", LeanVar(v)),
            Expr::Constant(c) => {
                match c {
                    Constant::Numeral(n) => write!(f, "{}", n),
                    Constant::Boolean(b) => write!(f, "{}", b),
                    Constant::String(s) => write!(f, "{}", s.display()),
                    Constant::Decimal(d) => write!(f, "{}", d.display()),
                    _ => todo!(),
                }
            }
            Expr::BinaryOp(bin_op, args) => {
                let bin_op_str = match bin_op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => "/",
                    BinOp::Mod => "%",
                };
                write!(f, "({} {} {})", LeanExpr(&args[0]), bin_op_str, LeanExpr(&args[1]))
            }
            Expr::Atom(bin_rel, args) => {
                let bin_rel_str = match bin_rel {
                    BinRel::Eq => "=",
                    BinRel::Ne => "≠",
                    BinRel::Le => "≤",
                    BinRel::Lt => "<",
                    BinRel::Ge => "≥",
                    BinRel::Gt => ">",
                };
                write!(f, "({} {} {})", LeanExpr(&args[0]), bin_rel_str, LeanExpr(&args[1]))
            }
            Expr::App(function, args) => {
                write!(
                    f,
                    "({} {})",
                    LeanExpr(function.as_ref()),
                    args.iter().map(LeanExpr).format(" ")
                )
            }
            Expr::And(exprs) => {
                write!(f, "({})", exprs.iter().map(LeanExpr).format(" && "))
            }
            Expr::Or(exprs) => {
                write!(f, "({})", exprs.iter().map(LeanExpr).format(" || "))
            }
            _ => todo!(),
        }
    }
}

impl<'a> fmt::Display for LeanFunDef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let LeanFunDef(FunDef { name, args, out, comment: _, body }) = self;
        writeln!(
            f,
            "def {} {} : {} :=",
            LeanVar(name),
            args.iter()
                .map(|(arg, arg_sort)| format!("({} : {})", LeanVar(arg), LeanSort(arg_sort)))
                .collect::<Vec<_>>()
                .join(" "),
            LeanSort(out)
        )?;
        writeln!(f, "  {}", LeanExpr(body))
    }
}

impl<'a> fmt::Display for LeanPred<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Pred::Expr(expr) => write!(f, "{}", LeanExpr(expr)),
            Pred::And(preds) => write!(f, "({})", preds.iter().map(LeanPred).format(" ∧ ")),
            Pred::KVar(_, _) => panic!("kvars should not appear when encoding in lean"),
        }
    }
}

impl<'a> fmt::Display for LeanConstraint<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Constraint::ForAll(bind, inner) => {
                if bind.pred.is_trivially_true() {
                    write!(
                        f,
                        "(∀ ({} : {}), {})",
                        LeanVar(&bind.name),
                        LeanSort(&bind.sort),
                        LeanConstraint(inner)
                    )
                } else {
                    write!(
                        f,
                        "(∀ ({} : {}), ({} -> {}))",
                        LeanVar(&bind.name),
                        LeanSort(&bind.sort),
                        LeanPred(&bind.pred),
                        LeanConstraint(inner)
                    )
                }
            }
            Constraint::Conj(constraints) => {
                write!(f, "({})", constraints.iter().map(LeanConstraint).format(" ∧ "))
            }
            Constraint::Pred(pred, _) => {
                write!(f, "{}", LeanPred(pred))
            }
        }
    }
}

impl<'genv, 'tcx> fmt::Display for LeanEncoder<'genv, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "-- GENERATED; DO NOT EDIT --")?;
        if !self.fun_defs().is_empty() {
            writeln!(f, "-- FUNCTIONS --")?;
            for fun_def in self.fun_defs() {
                writeln!(f, "{}", LeanFunDef(fun_def))?;
            }
        }
        if !self.constants().is_empty() {
            writeln!(f, "-- Constants --")?;
            for const_def in self.constants() {
                writeln!(f, "{}", LeanConstDef(const_def))?;
            }
        }
        writeln!(f, "-- THEOREM --")?;
        writeln!(
            f,
            "def {} : Prop := {}",
            self.theorem_name().replace(".", "_"),
            LeanConstraint(self.constraint())
        )
    }
}
