use core::fmt;
use std::fmt::Write;

use flux_common::dbg::as_subscript;
use flux_middle::{global_env::GlobalEnv, rty::ProvenanceMap};
use itertools::Itertools;
use liquid_fixpoint::{FixpointFmt, Identifier, ThyFunc};

use crate::fixpoint_encoding::fixpoint::{
    BinOp, BinRel, ConstDecl, Constant, Constraint, DataDecl, DataField, DataSort, Expr, FunDef,
    KVarDecl, LocalVar, Pred, Sort, SortCtor, SortDecl, Var,
};

pub struct LeanCtxt<'a, 'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    pub provenance_map: &'a ProvenanceMap<LocalVar>,
}

pub struct WithLeanCtxt<'a, 'b, 'genv, 'tcx, T> {
    pub item: T,
    pub cx: &'a LeanCtxt<'b, 'genv, 'tcx>,
}

impl<'a, 'b, 'genv, 'tcx, T: LeanFmt> fmt::Display for WithLeanCtxt<'a, 'b, 'genv, 'tcx, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.item.lean_fmt(f, self.cx)
    }
}

pub trait LeanFmt {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result;
}

struct LeanSort<'a>(&'a Sort);
pub struct LeanKConstraint<'a> {
    pub kvars: &'a [KVarDecl],
    pub constr: &'a Constraint,
}

pub struct LeanSortVar<'a>(pub &'a DataSort);
struct LeanKVarDecl<'a>(&'a KVarDecl);
struct LeanThyFunc<'a>(&'a ThyFunc);

impl LeanFmt for &SortDecl {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        (*self).lean_fmt(f, cx)
    }
}

impl LeanFmt for SortDecl {
    fn lean_fmt(&self, f: &mut fmt::Formatter, _cx: &LeanCtxt) -> fmt::Result {
        write!(
            f,
            "{} {} : Type",
            LeanSortVar(&self.name),
            (0..(self.vars))
                .map(|i| format!("(t{i} : Type) [Inhabited t{i}]"))
                .format(" ")
        )
    }
}

impl LeanFmt for &ConstDecl {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        (*self).lean_fmt(f, cx)
    }
}

impl LeanFmt for ConstDecl {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        self.name.lean_fmt(f, cx)?;
        write!(f, " : {}", LeanSort(&self.sort))
    }
}

impl LeanFmt for &DataField {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        (*self).lean_fmt(f, cx)
    }
}

impl LeanFmt for DataField {
    fn lean_fmt(&self, f: &mut fmt::Formatter, _cx: &LeanCtxt) -> fmt::Result {
        write!(
            f,
            "({} : {})",
            self.name.display().to_string().replace("$", "_"),
            LeanSort(&self.sort)
        )
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

impl LeanFmt for &DataDecl {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        (*self).lean_fmt(f, cx)
    }
}

impl LeanFmt for DataDecl {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        if self.ctors.len() == 1 {
            writeln!(f, "@[ext]")?;
            writeln!(
                f,
                "structure {} {} where",
                LeanSortVar(&self.name),
                (0..self.vars)
                    .map(|i| format!("(t{i} : Type) [Inhabited t{i}]"))
                    .format(" ")
            )?;
            writeln!(f, "  {}::", self.ctors[0].name.display().to_string().replace("$", "_"),)?;
            for field in &self.ctors[0].fields {
                write!(f, "  ")?;
                field.lean_fmt(f, cx)?;
                writeln!(f)?;
            }
        } else {
            writeln!(
                f,
                "inductive {} {} where",
                LeanSortVar(&self.name),
                (0..self.vars)
                    .map(|i| format!("(t{i} : Type) [Inhabited t{i}]"))
                    .format(" ")
            )?;
            for data_ctor in &self.ctors {
                write!(f, "| ")?;
                data_ctor.name.lean_fmt(f, cx)?;
                for field in &data_ctor.fields {
                    write!(f, " ")?;
                    field.lean_fmt(f, cx)?;
                }
                writeln!(f)?;
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
            ThyFunc::BvAshr => write!(f, "BitVec_sshiftRight"),
            ThyFunc::BvLshr => write!(f, "BitVec_ushiftRight"),
            ThyFunc::BvShl => write!(f, "BitVec_shiftLeft"),
            ThyFunc::BvSignExtend(size) => write!(f, "BitVec.signExtend {}", size),
            ThyFunc::BvZeroExtend(size) => write!(f, "BitVec.zeroExtend {}", size),
            ThyFunc::BvUrem => write!(f, "BitVec.umod"),
            ThyFunc::BvSge => write!(f, "BitVec_sge"),
            ThyFunc::BvSgt => write!(f, "BitVec_sgt"),
            ThyFunc::BvUge => write!(f, "BitVec_uge"),
            ThyFunc::BvUgt => write!(f, "BitVec_ugt"),
            ThyFunc::MapDefault => write!(f, "SmtMap_default"),
            ThyFunc::MapSelect => write!(f, "SmtMap_select"),
            ThyFunc::MapStore => write!(f, "SmtMap_store"),
            func => panic!("Unsupported theory function {}", func),
        }
    }
}

impl LeanFmt for &Var {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        (*self).lean_fmt(f, cx)
    }
}

impl LeanFmt for Var {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        match self {
            Var::Global(_gvar, Some(def_id)) => {
                let path = cx
                    .genv
                    .tcx()
                    .def_path(def_id.parent())
                    .to_filename_friendly_no_crate()
                    .replace("-", "_");
                if path.is_empty() {
                    write!(f, "{}", def_id.name())
                } else {
                    write!(f, "{path}_{}", def_id.name())
                }
            }
            Var::Local(local_var) => {
                write!(f, "{}", cx.provenance_map.get(*local_var))
            }
            Var::DataCtor(adt_id, _) | Var::DataProj { adt_id, field: _ } => {
                write!(
                    f,
                    "{}.{}",
                    LeanSortVar(&DataSort::Adt(*adt_id)),
                    self.display().to_string().replace("$", "_")
                )
            }
            Var::Param(param) => {
                // We start with a `₀` prefix to distinguish from the `LocalVar`
                write!(f, "{}₀{}", param.name, as_subscript(param.index))
            }
            _ => {
                write!(f, "{}", self.display().to_string().replace("$", "_"))
            }
        }
    }
}

impl<'a> fmt::Display for LeanSort<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Sort::Int => write!(f, "Int"),
            Sort::Bool => write!(f, "Prop"),
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
                    SortCtor::Map => {
                        write!(f, "(SmtMap {} {})", LeanSort(&args[0]), LeanSort(&args[1]))
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
                write!(f, "{{t{v} : Type}} -> [Inhabited t{v}] -> {}", LeanSort(sort.as_ref()))
            }
            Sort::Var(v) => write!(f, "t{v}"),
            s => todo!("{:?}", s),
        }
    }
}

impl LeanFmt for &Expr {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        (*self).lean_fmt(f, cx)
    }
}

impl LeanFmt for Expr {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        match self {
            Expr::Var(v) => v.lean_fmt(f, cx),
            Expr::Constant(c) => {
                match c {
                    Constant::Numeral(n) => write!(f, "{n}",),
                    Constant::Boolean(b) => write!(f, "{}", if *b { "True" } else { "False" }),
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
                write!(f, "(")?;
                args[0].lean_fmt(f, cx)?;
                write!(f, " {} ", bin_op_str)?;
                args[1].lean_fmt(f, cx)?;
                write!(f, ")")
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
                write!(f, "(")?;
                args[0].lean_fmt(f, cx)?;
                write!(f, " {} ", bin_rel_str)?;
                args[1].lean_fmt(f, cx)?;
                write!(f, ")")
            }
            Expr::App(function, sort_args, args) => {
                write!(f, "(")?;
                function.as_ref().lean_fmt(f, cx)?;
                if let Some(sort_args) = sort_args {
                    for (i, s_arg) in sort_args.iter().enumerate() {
                        write!(f, " (t{i} := {})", LeanSort(s_arg))?;
                    }
                }
                for arg in args {
                    write!(f, " ")?;
                    arg.lean_fmt(f, cx)?;
                }
                write!(f, ")")
            }
            Expr::And(exprs) => {
                write!(f, "(")?;
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        write!(f, " && ")?;
                    }
                    expr.lean_fmt(f, cx)?;
                }
                write!(f, ")")
            }
            Expr::Or(exprs) => {
                write!(f, "(")?;
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        write!(f, " || ")?;
                    }
                    expr.lean_fmt(f, cx)?;
                }
                write!(f, ")")
            }
            Expr::Neg(inner) => {
                write!(f, "(-")?;
                inner.as_ref().lean_fmt(f, cx)?;
                write!(f, ")")
            }
            Expr::IfThenElse(ite) => {
                let [condition, if_true, if_false] = ite.as_ref();
                write!(f, "(if ")?;
                condition.lean_fmt(f, cx)?;
                write!(f, " then ")?;
                if_true.lean_fmt(f, cx)?;
                write!(f, " else ")?;
                if_false.lean_fmt(f, cx)?;
                write!(f, ")")
            }
            Expr::Not(inner) => {
                write!(f, "(¬")?;
                inner.as_ref().lean_fmt(f, cx)?;
                write!(f, ")")
            }
            Expr::Imp(implication) => {
                let [lhs, rhs] = implication.as_ref();
                write!(f, "(")?;
                lhs.lean_fmt(f, cx)?;
                write!(f, " -> ")?;
                rhs.lean_fmt(f, cx)?;
                write!(f, ")")
            }
            Expr::Iff(equiv) => {
                let [lhs, rhs] = equiv.as_ref();
                write!(f, "(")?;
                lhs.lean_fmt(f, cx)?;
                write!(f, " <-> ")?;
                rhs.lean_fmt(f, cx)?;
                write!(f, ")")
            }
            Expr::Let(binder, exprs) => {
                let [def, body] = exprs.as_ref();
                write!(f, "(let ")?;
                binder.lean_fmt(f, cx)?;
                write!(f, " := ")?;
                def.lean_fmt(f, cx)?;
                write!(f, "; ")?;
                body.lean_fmt(f, cx)?;
                write!(f, ")")
            }
            Expr::ThyFunc(thy_func) => {
                write!(f, "{}", LeanThyFunc(thy_func))
            }
            Expr::IsCtor(..) => {
                todo!("not yet implemented: datatypes in lean")
            }
            Expr::Exists(..) => {
                todo!("not yet implemented: exists in lean")
            }
            Expr::BoundVar(_) => {
                unreachable!("bound vars should only be present in fixpoint output")
            }
        }
    }
}

impl LeanFmt for &FunDef {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        (*self).lean_fmt(f, cx)
    }
}

impl LeanFmt for FunDef {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        let FunDef { name, args, out, comment: _, body } = self;
        write!(f, "def ")?;
        name.lean_fmt(f, cx)?;
        for (arg, arg_sort) in args {
            write!(f, " (")?;
            arg.lean_fmt(f, cx)?;
            write!(f, " : {})", LeanSort(arg_sort))?;
        }
        writeln!(f, " : {} :=", LeanSort(out))?;
        write!(f, "  ")?;
        body.lean_fmt(f, cx)?;
        writeln!(f)
    }
}

impl LeanFmt for &Pred {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        (*self).lean_fmt(f, cx)
    }
}

impl LeanFmt for Pred {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        match self {
            Pred::Expr(expr) => expr.lean_fmt(f, cx),
            Pred::And(preds) => {
                write!(f, "(")?;
                for (i, pred) in preds.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ∧ ")?;
                    }
                    pred.lean_fmt(f, cx)?;
                }
                write!(f, ")")
            }
            Pred::KVar(kvid, args) => {
                write!(f, "({}", kvid.display().to_string().replace("$", "_"))?;
                for arg in args {
                    write!(f, " ")?;
                    arg.lean_fmt(f, cx)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl<'a> fmt::Display for LeanKVarDecl<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let sorts = self
            .0
            .sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| format!("(a{i} : {})", LeanSort(sort)))
            .format(" -> ");
        write!(f, "∃ {} : {} -> Prop", self.0.kvid.display().to_string().replace("$", "_"), sorts)
    }
}

impl<'a> LeanFmt for LeanKConstraint<'a> {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        if self.kvars.is_empty() {
            self.constr.lean_fmt(f, cx)
        } else {
            write!(f, "{}, ", self.kvars.iter().map(LeanKVarDecl).format(", "))?;
            self.constr.lean_fmt(f, cx)
        }
    }
}

impl LeanFmt for &Constraint {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        (*self).lean_fmt(f, cx)
    }
}

impl LeanFmt for Constraint {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        let mut fmt_cx = ConstraintFormatter::default();
        fmt_cx.incr();
        fmt_cx.newline(f)?;
        self.fmt_nested(f, cx, &mut fmt_cx)?;
        fmt_cx.decr();
        Ok(())
    }
}

impl FormatNested for Constraint {
    fn fmt_nested(
        &self,
        f: &mut fmt::Formatter,
        lean_cx: &LeanCtxt,
        fmt_cx: &mut ConstraintFormatter,
    ) -> fmt::Result {
        match self {
            Constraint::ForAll(bind, inner) => {
                let trivial_pred = bind.pred.is_trivially_true();
                let trivial_bind = bind.name.display().to_string().starts_with("_");
                if !trivial_bind {
                    write!(f, "∀ (")?;
                    bind.name.lean_fmt(f, lean_cx)?;
                    write!(f, " : {}),", LeanSort(&bind.sort))?;
                    fmt_cx.incr();
                    fmt_cx.newline(f)?;
                }
                if !trivial_pred {
                    bind.pred.lean_fmt(f, lean_cx)?;
                    write!(f, " ->")?;
                    fmt_cx.incr();
                    fmt_cx.newline(f)?;
                }
                inner.fmt_nested(f, lean_cx, fmt_cx)?;
                if !trivial_pred {
                    fmt_cx.decr();
                }
                if !trivial_bind {
                    fmt_cx.decr();
                }
                Ok(())
            }
            Constraint::Conj(constraints) => {
                let n = constraints.len();
                for (i, constraint) in constraints.iter().enumerate() {
                    constraint.fmt_nested(f, lean_cx, fmt_cx)?;
                    if i < n - 1 {
                        write!(f, " ∧")?;
                    }
                    fmt_cx.newline(f)?;
                }
                Ok(())
            }
            Constraint::Pred(pred, _) => pred.lean_fmt(f, lean_cx),
        }
    }
}

pub trait FormatNested {
    fn fmt_nested(
        &self,
        f: &mut fmt::Formatter,
        lean_cx: &LeanCtxt,
        fmt_cx: &mut ConstraintFormatter,
    ) -> fmt::Result;
}

#[derive(Default)]
pub struct ConstraintFormatter {
    level: u32,
}

impl ConstraintFormatter {
    pub fn incr(&mut self) {
        self.level += 1;
    }

    pub fn decr(&mut self) {
        self.level -= 1;
    }

    pub fn newline(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_char('\n')?;
        self.padding(f)
    }

    pub fn padding(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for _ in 0..self.level {
            f.write_str(" ")?;
        }
        Ok(())
    }
}
