use core::fmt;

use flux_middle::global_env::GlobalEnv;
use itertools::Itertools;
use liquid_fixpoint::{FixpointFmt, Identifier, ThyFunc};

use crate::fixpoint_encoding::fixpoint::{
    BinOp, BinRel, ConstDecl, Constant, Constraint, SortDecl, DataDecl, DataField, DataSort, Expr, FunDef,
    Pred, Sort, SortCtor, Var,
};

pub struct LeanSort<'a>(pub &'a Sort);
pub struct LeanFunDef<'a, 'genv, 'tcx>(pub &'a FunDef, pub GlobalEnv<'genv, 'tcx>);
pub struct LeanSortDecl<'a, 'genv, 'tcx>(pub &'a SortDecl, pub GlobalEnv<'genv, 'tcx>);
pub struct LeanDataDecl<'a, 'genv, 'tcx>(pub &'a DataDecl, pub GlobalEnv<'genv, 'tcx>);
pub struct LeanConstDecl<'a, 'genv, 'tcx>(pub &'a ConstDecl, pub GlobalEnv<'genv, 'tcx>);
pub struct LeanSortVar<'a>(pub &'a DataSort);
pub struct LeanDataField<'a, 'genv, 'tcx>(pub &'a DataField, pub GlobalEnv<'genv, 'tcx>);
pub struct LeanConstraint<'a, 'genv, 'tcx>(pub &'a Constraint, pub GlobalEnv<'genv, 'tcx>);
struct LeanPred<'a, 'genv, 'tcx>(&'a Pred, GlobalEnv<'genv, 'tcx>);
struct LeanExpr<'a, 'genv, 'tcx>(&'a Expr, GlobalEnv<'genv, 'tcx>);
pub struct LeanVar<'a, 'genv, 'tcx>(pub &'a Var, pub GlobalEnv<'genv, 'tcx>);
struct LeanThyFunc<'a>(&'a ThyFunc);

impl<'a, 'genv, 'tcx> fmt::Display for LeanSortDecl<'a, 'genv, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
                f,
                "{} {} : Type",
                LeanSortVar(&self.0.name),
                (0..(self.0.vars))
                    .map(|i| format!("(t{i} : Type)"))
                    .format(" ")
            )
    }
}

impl<'a, 'genv, 'tcx> fmt::Display for LeanConstDecl<'a, 'genv, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", LeanVar(&self.0.name, self.1), LeanSort(&self.0.sort))
    }
}

impl<'a, 'genv, 'tcx> fmt::Display for LeanDataField<'a, 'genv, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} : {})", LeanVar(&self.0.name, self.1), LeanSort(&self.0.sort))
    }
}

impl<'a> fmt::Display for LeanSortVar<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            DataSort::User(def_id) => write!(f, "{}", def_id.name()),
            _ => write!(f, "{}", self.0.display().to_string().replace("$", "_")),
        }
    }
}

impl<'a, 'genv, 'tcx> fmt::Display for LeanDataDecl<'a, 'genv, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.ctors.len() == 1 {
            writeln!(f, "structure {} where", LeanSortVar(&self.0.name))?;
            for field in &self.0.ctors[0].fields {
                writeln!(f, "  {}", LeanDataField(field, self.1))?;
            }
        } else {
            writeln!(f, "inductive {} where", LeanSortVar(&self.0.name))?;
            for data_ctor in &self.0.ctors {
                writeln!(
                    f,
                    "| {} {}",
                    LeanVar(&data_ctor.name, self.1),
                    data_ctor
                        .fields
                        .iter()
                        .map(|field| LeanDataField(field, self.1))
                        .format(" ")
                )?;
            }
        }
        Ok(())
    }
}

impl<'a> fmt::Display for LeanThyFunc<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            ThyFunc::IntToBv8 => write!(f, "BitVec.ofInt 8"),
            ThyFunc::IntToBv32 => write!(f, "BitVec.ofInt 32"),
            ThyFunc::IntToBv64 => write!(f, "BitVec.ofInt 64"),
            ThyFunc::Bv8ToInt | ThyFunc::Bv32ToInt | ThyFunc::Bv64ToInt => {
                write!(f, "BitVec.toNat")
            }
            ThyFunc::BvAdd => write!(f, "BitVec.add"),
            ThyFunc::BvSub => write!(f, "BitVec.sub"),
            ThyFunc::BvMul => write!(f, "BitVec.mul"),
            ThyFunc::BvNeg => write!(f, "BitVec.neg"),
            ThyFunc::BvSdiv => write!(f, "BitVec.sdiv"),
            ThyFunc::BvSrem => write!(f, "BitVec.srem"),
            ThyFunc::BvUdiv => write!(f, "BitVec.udiv"),
            ThyFunc::BvAnd => write!(f, "BitVec.and"),
            ThyFunc::BvOr => write!(f, "BitVec.or"),
            ThyFunc::BvXor => write!(f, "BitVec.xor"),
            ThyFunc::BvNot => write!(f, "BitVec.not"),
            ThyFunc::BvSle => write!(f, "BitVec.sle"),
            ThyFunc::BvSlt => write!(f, "BitVec.slt"),
            ThyFunc::BvUle => write!(f, "BitVec.ule"),
            ThyFunc::BvUlt => write!(f, "BitVec.ult"),
            ThyFunc::BvAshr => write!(f, "BitVec.sshiftRight"),
            ThyFunc::BvLshr => write!(f, "BitVec.ushiftRight"),
            ThyFunc::BvShl => write!(f, "BitVec.shiftLeft"),
            ThyFunc::BvSignExtend(size) => write!(f, "BitVec.signExtend {}", size),
            ThyFunc::BvZeroExtend(size) => write!(f, "BitVec.zeroExtend {}", size),
            ThyFunc::BvUrem | ThyFunc::BvSge | ThyFunc::BvSgt | ThyFunc::BvUge | ThyFunc::BvUgt => {
                todo!("No builtin {}, define a local function {} and call it here", self.0, self.0)
            }
            func => panic!("Unsupported theory function {}", func),
        }
    }
}

impl<'a, 'genv, 'tcx> fmt::Display for LeanVar<'a, 'genv, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Var::Global(_gvar, Some(def_id)) = self.0 {
            let path = self
                .1
                .tcx()
                .def_path(def_id.parent())
                .to_filename_friendly_no_crate()
                .replace("-", "_");
            if path.is_empty() {
                write!(f, "{}", def_id.name())
            } else {
                write!(f, "{path}_{}", def_id.name())
            }
        } else {
            write!(f, "{}", self.0.display().to_string().replace("$", "_"))
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
            Sort::App(sort_ctor, args) => {
                match sort_ctor {
                    SortCtor::Data(sort) => {
                        if args.is_empty() {
                            write!(f, "{}", LeanSortVar(sort))
                        } else {
                            write!(
                                f,
                                "({} {})",
                                LeanSortVar(sort),
                                args.iter().map(LeanSort).format(" ")
                            )
                        }
                    }
                    _ => todo!(),
                }
            }
            Sort::BitVec(bv_size) => {
                match bv_size.as_ref() {
                    Sort::BvSize(size) => write!(f, "BitVec {}", size),
                    s => panic!("encountered sort {} where bitvec size was expected", LeanSort(s)),
                }
            }
            Sort::Abs(v, sort) => {
                write!(f, "{{t{v} : Type}} -> {}", LeanSort(sort.as_ref()))
            }
            Sort::Var(v) => write!(f, "t{v}"),
            s => todo!("{:?}", s),
        }
    }
}

impl<'a, 'genv, 'tcx> fmt::Display for LeanExpr<'a, 'genv, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Expr::Var(v) => write!(f, "{}", LeanVar(v, self.1)),
            Expr::Constant(c) => {
                match c {
                    Constant::Numeral(n) => write!(f, "{n}",),
                    Constant::Boolean(b) => write!(f, "{b}"),
                    Constant::String(s) => write!(f, "{}", s.display()),
                    Constant::Real(n) => write!(f, "{n}.0"),
                    Constant::BitVec(bv, size) => write!(f, "{}#{}", bv, size),
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
                write!(
                    f,
                    "({} {} {})",
                    LeanExpr(&args[0], self.1),
                    bin_op_str,
                    LeanExpr(&args[1], self.1)
                )
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
                write!(
                    f,
                    "({} {} {})",
                    LeanExpr(&args[0], self.1),
                    bin_rel_str,
                    LeanExpr(&args[1], self.1)
                )
            }
            Expr::App(function, args) => {
                write!(
                    f,
                    "({} {})",
                    LeanExpr(function.as_ref(), self.1),
                    args.iter().map(|arg| LeanExpr(arg, self.1)).format(" ")
                )
            }
            Expr::And(exprs) => {
                write!(
                    f,
                    "({})",
                    exprs
                        .iter()
                        .map(|expr| LeanExpr(expr, self.1))
                        .format(" && ")
                )
            }
            Expr::Or(exprs) => {
                write!(
                    f,
                    "({})",
                    exprs
                        .iter()
                        .map(|expr| LeanExpr(expr, self.1))
                        .format(" || ")
                )
            }
            Expr::Neg(inner) => {
                write!(f, "(-{})", LeanExpr(inner.as_ref(), self.1))
            }
            Expr::IfThenElse(ite) => {
                let [condition, if_true, if_false] = ite.as_ref();
                write!(
                    f,
                    "(if {} then {} else {})",
                    LeanExpr(condition, self.1),
                    LeanExpr(if_true, self.1),
                    LeanExpr(if_false, self.1)
                )
            }
            Expr::Not(inner) => {
                write!(f, "(¬{})", LeanExpr(inner.as_ref(), self.1))
            }
            Expr::Imp(implication) => {
                let [lhs, rhs] = implication.as_ref();
                write!(f, "({} -> {})", LeanExpr(lhs, self.1), LeanExpr(rhs, self.1))
            }
            Expr::Iff(equiv) => {
                let [lhs, rhs] = equiv.as_ref();
                write!(f, "({} <-> {})", LeanExpr(lhs, self.1), LeanExpr(rhs, self.1))
            }
            Expr::Let(binder, exprs) => {
                let [def, body] = exprs.as_ref();
                write!(
                    f,
                    "(let {} := {}; {})",
                    LeanVar(binder, self.1),
                    LeanExpr(def, self.1),
                    LeanExpr(body, self.1)
                )
            }
            Expr::ThyFunc(thy_func) => {
                write!(f, "{}", LeanThyFunc(thy_func))
            }
            Expr::IsCtor(..) => {
                todo!("not yet implemented: datatypes in lean")
            }
        }
    }
}

impl<'a, 'genv, 'tcx> fmt::Display for LeanFunDef<'a, 'genv, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let LeanFunDef(FunDef { name, args, out, comment: _, body }, _) = self;
        writeln!(
            f,
            "def {} {} : {} :=",
            LeanVar(name, self.1),
            args.iter()
                .map(|(arg, arg_sort)| {
                    format!("({} : {})", LeanVar(arg, self.1), LeanSort(arg_sort))
                })
                .collect::<Vec<_>>()
                .join(" "),
            LeanSort(out)
        )?;
        writeln!(f, "  {}", LeanExpr(body, self.1))
    }
}

impl<'a, 'genv, 'tcx> fmt::Display for LeanPred<'a, 'genv, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Pred::Expr(expr) => write!(f, "{}", LeanExpr(expr, self.1)),
            Pred::And(preds) => {
                write!(
                    f,
                    "({})",
                    preds
                        .iter()
                        .map(|pred| LeanPred(pred, self.1))
                        .format(" ∧ ")
                )
            }
            Pred::KVar(_, _) => panic!("kvars should not appear when encoding in lean"),
        }
    }
}

impl<'a, 'genv, 'tcx> fmt::Display for LeanConstraint<'a, 'genv, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Constraint::ForAll(bind, inner) => {
                if bind.pred.is_trivially_true() {
                    write!(
                        f,
                        "(∀ ({} : {}), {})",
                        LeanVar(&bind.name, self.1),
                        LeanSort(&bind.sort),
                        LeanConstraint(inner, self.1)
                    )
                } else {
                    write!(
                        f,
                        "(∀ ({} : {}), ({} -> {}))",
                        LeanVar(&bind.name, self.1),
                        LeanSort(&bind.sort),
                        LeanPred(&bind.pred, self.1),
                        LeanConstraint(inner, self.1)
                    )
                }
            }
            Constraint::Conj(constraints) => {
                write!(
                    f,
                    "({})",
                    constraints
                        .iter()
                        .map(|constraint| LeanConstraint(constraint, self.1))
                        .format(" ∧ ")
                )
            }
            Constraint::Pred(pred, _) => {
                write!(f, "{}", LeanPred(pred, self.1))
            }
        }
    }
}
