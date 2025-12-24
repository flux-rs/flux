use core::fmt;
use std::{collections::HashMap, fmt::Write};

use flux_common::{
    bug,
    dbg::{self, as_subscript},
};
use flux_middle::{
    global_env::GlobalEnv,
    rty::{PrettyMap, PrettyVar},
};
use itertools::Itertools;
use liquid_fixpoint::{FixpointFmt, Identifier, ThyFunc};
use rustc_data_structures::fx::FxIndexSet;
use rustc_hir::def_id::DefId;

use crate::fixpoint_encoding::{
    FixpointSolution,
    fixpoint::{
        self, AdtId, BinOp, BinRel, ConstDecl, Constant, Constraint, DataDecl, DataField, DataSort,
        Expr, FunDef, KVarDecl, KVid, LocalVar, Pred, Sort, SortCtor, SortDecl, Var,
    },
};

pub struct LeanCtxt<'a, 'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    pub pretty_var_map: &'a PrettyMap<LocalVar>,
    pub adt_map: &'a FxIndexSet<DefId>,
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

pub struct LeanKConstraint<'a> {
    pub theorem_name: &'a str,
    pub kvars: &'a [KVarDecl],
    pub constr: &'a Constraint,
    pub kvar_solutions: HashMap<KVid, FixpointSolution>,
}

struct LeanThyFunc<'a>(&'a ThyFunc);

impl LeanFmt for SortDecl {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        self.name.lean_fmt(f, cx)?;
        write!(
            f,
            " {} : Type",
            (0..(self.vars))
                .map(|i| format!("(t{i} : Type) [Inhabited t{i}]"))
                .format(" ")
        )
    }
}

impl LeanFmt for ConstDecl {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        self.name.lean_fmt(f, cx)?;
        write!(f, " : {}", WithLeanCtxt { item: &self.sort, cx })
    }
}

// TODO(lean-localize-imports) this seems wrong, but related to lack of storing `VariantIdx` in the `DataProj`
impl LeanFmt for DataField {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        write!(
            f,
            "({} : {})",
            self.name.display().to_string().replace("$", "_"),
            WithLeanCtxt { item: &self.sort, cx }
        )
    }
}

impl LeanFmt for DataSort {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> std::fmt::Result {
        match self {
            DataSort::User(def_id) => write!(f, "{}", def_id.name()),
            DataSort::Tuple(n) => write!(f, "Tupleₓ{}", dbg::as_subscript(n)),
            DataSort::Adt(adt_id) => {
                let def_id = cx.adt_map.get_index(adt_id.as_usize()).unwrap();
                write!(f, "{}", def_id_to_pascal_case(def_id, &cx.genv.tcx()))
            }
        }
    }
}

impl LeanFmt for DataDecl {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        if self.ctors.len() == 1 {
            writeln!(f, "@[ext]")?;
            write!(f, "structure ")?;
            self.name.lean_fmt(f, cx)?;
            writeln!(
                f,
                " {} where",
                (0..self.vars)
                    .map(|i| format!("(t{i} : Type) [Inhabited t{i}]"))
                    .format(" ")
            )?;
            writeln!(f, "  {} ::", WithLeanCtxt { item: &self.ctors[0].name, cx })?;
            let ctor = &self.ctors[0];
            if let fixpoint::Var::DataCtor(adt_id, _) = &ctor.name {
                for (idx, field) in ctor.fields.iter().enumerate() {
                    writeln!(
                        f,
                        "    {} : {} ",
                        WithLeanCtxt { item: LeanField(*adt_id, idx.try_into().unwrap()), cx },
                        WithLeanCtxt { item: &field.sort, cx }
                    )?;
                }
            } else {
                bug!("unexpected ctor {ctor:?} in datadecl");
            };
        } else {
            write!(f, "inductive ")?;
            self.name.lean_fmt(f, cx)?;
            writeln!(
                f,
                " {} where",
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

impl<T: LeanFmt> LeanFmt for &T {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        (*self).lean_fmt(f, cx)
    }
}

struct LeanAdt(AdtId);
struct LeanDataProj(AdtId, u32);
struct LeanField(AdtId, u32);

impl LeanFmt for LeanField {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        let adt_id = self.0;
        if let Some(def_id) = cx.adt_map.get_index(adt_id.as_usize())
            && let Ok(adt_sort_def) = cx.genv.adt_sort_def_of(def_id)
        {
            write!(f, "{}", adt_sort_def.struct_variant().field_names()[self.1 as usize])
        } else {
            write!(f, "fld{}", as_subscript(self.1 as usize))
        }
    }
}

impl LeanFmt for LeanAdt {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        let def_id = cx.adt_map.get_index(self.0.as_usize()).unwrap();
        write!(f, "{}", def_id_to_pascal_case(def_id, &cx.genv.tcx()))
    }
}

impl LeanFmt for LeanDataProj {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        write!(
            f,
            "{}.{}",
            WithLeanCtxt { item: LeanAdt(self.0), cx },
            WithLeanCtxt { item: LeanField(self.0, self.1), cx }
        )
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
            Var::DataCtor(adt_id, idx) => {
                write!(
                    f,
                    "mk{}{}",
                    WithLeanCtxt { item: &DataSort::Adt(*adt_id), cx },
                    as_subscript(idx.as_usize())
                )
            }
            Var::DataProj { adt_id, field } => LeanDataProj(*adt_id, *field).lean_fmt(f, cx),
            Var::Local(local_var) => {
                write!(f, "{}", cx.pretty_var_map.get(&PrettyVar::Local(*local_var)))
            }
            Var::Param(param) => {
                write!(f, "{}", cx.pretty_var_map.get(&PrettyVar::Param(*param)))
            }
            _ => {
                write!(f, "{}", self.display().to_string().replace("$", "_"))
            }
        }
    }
}

impl LeanFmt for Sort {
    fn lean_fmt(&self, f: &mut std::fmt::Formatter, cx: &LeanCtxt) -> std::fmt::Result {
        match self {
            Sort::Int => write!(f, "Int"),
            Sort::Bool => write!(f, "Bool"),
            Sort::Real => write!(f, "Real"),
            Sort::Str => write!(f, "String"),
            Sort::Func(f_sort) => {
                write!(
                    f,
                    "({} -> {})",
                    WithLeanCtxt { item: &f_sort[0], cx },
                    WithLeanCtxt { item: &f_sort[1], cx }
                )
            }
            Sort::App(sort_ctor, args) => {
                match sort_ctor {
                    SortCtor::Data(sort) => {
                        if args.is_empty() {
                            sort.lean_fmt(f, cx)
                        } else {
                            write!(
                                f,
                                "({} {})",
                                WithLeanCtxt { item: sort, cx },
                                args.iter()
                                    .map(|arg| { WithLeanCtxt { item: arg, cx } })
                                    .format(" ")
                            )
                        }
                    }
                    SortCtor::Map => {
                        write!(
                            f,
                            "(SmtMap {} {})",
                            WithLeanCtxt { item: &args[0], cx },
                            WithLeanCtxt { item: &args[1], cx }
                        )
                    }
                    _ => todo!(),
                }
            }
            Sort::BitVec(bv_size) => {
                match bv_size.as_ref() {
                    Sort::BvSize(size) => write!(f, "BitVec {}", size),
                    s => {
                        panic!(
                            "encountered sort {} where bitvec size was expected",
                            WithLeanCtxt { item: s, cx }
                        )
                    }
                }
            }
            Sort::Abs(v, sort) => {
                write!(
                    f,
                    "{{t{v} : Type}} -> [Inhabited t{v}] -> {}",
                    WithLeanCtxt { item: sort.as_ref(), cx }
                )
            }
            Sort::Var(v) => write!(f, "t{v}"),
            s => todo!("{:?}", s),
        }
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
                        write!(f, " (t{i} := {})", WithLeanCtxt { item: s_arg, cx })?;
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
                        write!(f, " ∧ ")?;
                    }
                    expr.lean_fmt(f, cx)?;
                }
                write!(f, ")")
            }
            Expr::Or(exprs) => {
                write!(f, "(")?;
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ∨ ")?;
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
            Expr::Exists(bind, expr) => {
                write!(f, "(∃ ")?;
                for (var, sort) in bind {
                    write!(f, "(")?;
                    var.lean_fmt(f, cx)?;
                    write!(f, " : {})", WithLeanCtxt { item: sort, cx })?;
                }
                write!(f, ", ")?;
                expr.lean_fmt(f, cx)?;
                write!(f, ")")?;
                Ok(())
            }
        }
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
            write!(f, " : {})", WithLeanCtxt { item: arg_sort, cx })?;
        }
        writeln!(f, " : {} :=", WithLeanCtxt { item: out, cx })?;
        write!(f, "  ")?;
        body.lean_fmt(f, cx)?;
        writeln!(f)
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

impl LeanFmt for KVarDecl {
    fn lean_fmt(&self, f: &mut std::fmt::Formatter, cx: &LeanCtxt) -> std::fmt::Result {
        let sorts = self
            .sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| format!("(a{i} : {})", WithLeanCtxt { item: sort, cx }))
            .format(" -> ");
        write!(f, "∃ {} : {} -> Prop", self.kvid.display().to_string().replace("$", "_"), sorts)
    }
}

impl LeanFmt for (&KVid, &FixpointSolution) {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        let (kvid, (binder, inner)) = self;
        write!(f, "def k{} ", kvid.as_usize())?;
        for (arg, sort) in binder {
            write!(f, "(")?;
            arg.lean_fmt(f, cx)?;
            write!(f, " : {}) ", WithLeanCtxt { item: sort, cx })?;
        }
        writeln!(f, ": Prop :=")?;
        write!(f, "  ")?;
        inner.lean_fmt(f, cx)?;
        Ok(())
    }
}

impl<'a> LeanFmt for LeanKConstraint<'a> {
    fn lean_fmt(&self, f: &mut fmt::Formatter, cx: &LeanCtxt) -> fmt::Result {
        // TODO(RJ): what is this filtering about?
        let _kvars: Vec<_> = self
            .kvars
            .iter()
            .filter(|kvar| !self.kvar_solutions.contains_key(&kvar.kvid))
            .collect();

        if !self.kvar_solutions.is_empty() {
            writeln!(f, "namespace KVarSolutions\n")?;
            for kvar_solution in &self.kvar_solutions {
                kvar_solution.lean_fmt(f, cx)?;
            }
            writeln!(f, "\nend KVarSolutions\n\n")?;
            writeln!(f, "open KVarSolutions\n\n")?;
        }

        write!(f, "\n\ndef {} := ", self.theorem_name.replace(".", "_"))?;

        if self.kvars.is_empty() {
            self.constr.lean_fmt(f, cx)
        } else {
            write!(
                f,
                "{}, ",
                self.kvars
                    .iter()
                    .map(|kvar| WithLeanCtxt { item: kvar, cx })
                    .format(", ")
            )?;
            self.constr.lean_fmt(f, cx)
        }
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
                    write!(f, " : {}),", WithLeanCtxt { item: &bind.sort, cx: lean_cx })?;
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
                    write!(f, "(")?;
                    constraint.fmt_nested(f, lean_cx, fmt_cx)?;
                    write!(f, ")")?;
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

pub fn def_id_to_pascal_case(def_id: &DefId, tcx: &rustc_middle::ty::TyCtxt) -> String {
    let snake = tcx
        .def_path(*def_id)
        .to_filename_friendly_no_crate()
        .replace("-", "_");
    snake_case_to_pascal_case(&snake)
}

pub fn snake_case_to_pascal_case(snake: &str) -> String {
    snake
        .split('_')
        .filter(|s| !s.is_empty()) // skip empty segments (handles double underscores)
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                Some(first) => first.to_ascii_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect::<String>()
}
