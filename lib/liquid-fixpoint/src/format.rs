use std::fmt::{self, Write};

use itertools::Itertools;

use crate::{
    BinOp, BinRel, ConstDecl, Constant, Constraint, DataCtor, DataDecl, DataField, Expr,
    FixpointFmt, FunConstant, FunDef, Identifier, KVarDecl, Pred, Qualifier, Sort, SortCtor, Task,
    Types, constraint::BoundVar,
};

pub(crate) fn fmt_constraint<T: Types>(
    cstr: &Constraint<T>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    let mut cx = ConstraintFormatter::default();
    write!(f, "(constraint")?;
    cx.incr();
    cx.newline(f)?;
    cx.fmt_constraint(f, cstr)?;
    cx.decr();
    writeln!(f, ")")
}

impl<T: Types> fmt::Display for Constraint<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_constraint(self, f)
    }
}

impl<T: Types> fmt::Display for Task<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.ple {
            writeln!(f, "(fixpoint \"--rewrite\")")?;
        }
        if self.scrape_quals {
            writeln!(f, "(fixpoint \"--scrape=both\")")?;
        }
        for line in &self.comments {
            writeln!(f, ";; {line}")?;
        }
        writeln!(f)?;

        for data_decl in &self.data_decls {
            writeln!(f, "{data_decl}")?;
        }

        for qualif in &self.qualifiers {
            writeln!(f, "{qualif}")?;
        }

        for cinfo in &self.constants {
            writeln!(f, "{cinfo}")?;
        }

        for fun_decl in &self.define_funs {
            // fixpoint quirk where recursive functions must *also* be declared as constants
            if fun_decl.recursive {
                writeln!(f, "{}", fun_decl.as_constant())?;
            }
            writeln!(f, "{fun_decl}")?;
        }

        for kvar in &self.kvars {
            writeln!(f, "{kvar}")?;
        }

        writeln!(f)?;
        fmt_constraint(&self.constraint, f)
    }
}

impl<T: Types> fmt::Display for KVarDecl<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(var ${} ({})) ;; {}",
            self.kvid.display(),
            self.sorts.iter().format(" "),
            self.comment
        )
    }
}

impl<T: Types> fmt::Display for ConstDecl<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(constant {} {})", self.name.display(), self.sort)?;
        if let Some(comment) = &self.comment {
            write!(f, "  ;; {comment}")?;
        }
        Ok(())
    }
}

impl<T: Types> fmt::Debug for Task<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[derive(Default)]
struct ConstraintFormatter {
    level: u32,
}

impl ConstraintFormatter {
    fn fmt_constraint<T: Types>(
        &mut self,
        f: &mut fmt::Formatter<'_>,
        cstr: &Constraint<T>,
    ) -> fmt::Result {
        match cstr {
            Constraint::Pred(pred, tag) => self.fmt_pred_in_head_position(pred, tag.as_ref(), f),
            Constraint::Conj(cstrs) => {
                match &cstrs[..] {
                    [] => write!(f, "((true))"),
                    [cstr] => self.fmt_constraint(f, cstr),
                    cstrs => {
                        write!(f, "(and")?;
                        for cstr in cstrs {
                            self.incr();
                            self.newline(f)?;
                            self.fmt_constraint(f, cstr)?;
                            self.decr();
                        }
                        f.write_char(')')
                    }
                }
            }
            Constraint::ForAll(bind, head) => {
                write!(f, "(forall (({} {}) {})", bind.name.display(), bind.sort, bind.pred)?;

                self.incr();
                self.newline(f)?;
                self.fmt_constraint(f, head)?;
                self.decr();

                f.write_str(")")
            }
        }
    }

    fn fmt_pred_in_head_position<T: Types>(
        &mut self,
        pred: &Pred<T>,
        tag: Option<&T::Tag>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match pred {
            Pred::And(preds) => {
                match &preds[..] {
                    [] => write!(f, "((true))"),
                    [pred] => self.fmt_pred_in_head_position(pred, tag, f),
                    _ => {
                        write!(f, "(and")?;
                        for pred in preds {
                            self.incr();
                            self.newline(f)?;
                            self.fmt_pred_in_head_position(pred, tag, f)?;
                            self.decr();
                        }
                        write!(f, ")")
                    }
                }
            }
            Pred::Expr(_) | Pred::KVar(..) => {
                if let Some(tag) = tag {
                    write!(f, "(tag {pred} \"{tag}\")")
                } else {
                    write!(f, "{pred}")
                }
            }
        }
    }

    fn incr(&mut self) {
        self.level += 1;
    }

    fn decr(&mut self) {
        self.level -= 1;
    }

    fn newline(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_char('\n')?;
        self.padding(f)
    }

    fn padding(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for _ in 0..self.level {
            f.write_str(" ")?;
        }
        Ok(())
    }
}

impl<T: Types> fmt::Display for DataDecl<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(datatype ({} {}) ({}))",
            self.name.display(),
            self.vars,
            self.ctors.iter().format(" ")
        )
    }
}

impl<T: Types> fmt::Display for DataCtor<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} ({}))", self.name.display(), self.fields.iter().format(" "))
    }
}

impl<T: Types> fmt::Display for DataField<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.name.display(), self.sort)
    }
}

impl<T: Types> fmt::Display for SortCtor<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SortCtor::Set => write!(f, "Set_Set"),
            SortCtor::Map => write!(f, "Map_t"),
            SortCtor::Data(name) => write!(f, "{}", name.display()),
        }
    }
}

impl<T: Types> fmt::Display for Sort<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Int => write!(f, "int"),
            Sort::Bool => write!(f, "bool"),
            Sort::Real => write!(f, "real"),
            Sort::Str => write!(f, "Str"),
            Sort::Var(i) => write!(f, "@({i})"),
            Sort::BitVec(size) => write!(f, "(BitVec {size})"),
            Sort::BvSize(size) => write!(f, "Size{size}"),
            Sort::Abs(..) => {
                let (params, sort) = self.peel_out_abs();
                fmt_func(params, sort, f)
            }
            Sort::Func(..) => fmt_func(0, self, f),
            Sort::App(ctor, args) => {
                write!(f, "({ctor}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
        }
    }
}

fn fmt_func<T: Types>(params: usize, sort: &Sort<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "(func {params} (")?;
    let mut curr = sort;
    while let Sort::Func(input_and_output) = curr {
        let [input, output] = &**input_and_output;
        write!(f, "{input} ")?;
        curr = output;
    }
    write!(f, ") {curr})")
}

impl<T: Types> fmt::Display for Pred<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pred::And(preds) => {
                match &preds[..] {
                    [] => write!(f, "((true))"),
                    [pred] => write!(f, "{pred}"),
                    preds => write!(f, "(and {})", preds.iter().join(" ")),
                }
            }
            Pred::KVar(kvid, args) => {
                write!(f, "(${} {})", kvid.display(), args.iter().join(" "),)
            }
            Pred::Expr(expr) => write!(f, "({expr})"),
        }
    }
}

impl<T: Types> fmt::Display for Expr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Constant(c) => write!(f, "{c}"),
            Expr::Var(x) => write!(f, "{}", x.display()),
            Expr::App(func, _sort_args, args) => {
                write!(f, "({func} {})", args.iter().format(" "))
            }
            Expr::Neg(e) => {
                write!(f, "(- {e})")
            }
            Expr::BinaryOp(op, exprs) => {
                let [e1, e2] = &**exprs;
                write!(f, "({op} {e1} {e2})")
            }
            Expr::IfThenElse(exprs) => {
                let [p, e1, e2] = &**exprs;
                write!(f, "(if {p} {e1} {e2})")
            }
            Expr::And(exprs) => {
                write!(f, "(and {})", exprs.iter().format(" "))
            }
            Expr::Or(exprs) => {
                write!(f, "(or {})", exprs.iter().format(" "))
            }
            Expr::Not(e) => {
                write!(f, "(not {e})")
            }
            Expr::Imp(exprs) => {
                let [e1, e2] = &**exprs;
                write!(f, "(=> {e1} {e2})")
            }
            Expr::Iff(exprs) => {
                let [e1, e2] = &**exprs;
                write!(f, "(<=> {e1} {e2})")
            }
            Expr::Atom(rel, exprs) => {
                let [e1, e2] = &**exprs;
                write!(f, "({rel} {e1} {e2})")
            }
            Expr::Let(name, exprs) => {
                // Fixpoint only support one binder per let expressions, but it parses a singleton
                // list of binders to be forward-compatible
                let [e1, e2] = &**exprs;
                write!(f, "(let (({} {e1})) {e2})", name.display())
            }
            Expr::ThyFunc(thy_func) => write!(f, "{}", thy_func),
            Expr::IsCtor(ctor, e) => {
                write!(f, "(is${} {})", ctor.display(), e)
            }
            Expr::Exists(sorts, body) => {
                write!(f, "(exists ({}) {})", sorts.iter().format(" "), body)
            }
            Expr::BoundVar(BoundVar { level, idx }) => {
                write!(f, "bv{level}_{idx}")
            }
        }
    }
}

impl<T: Types> fmt::Display for Constant<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Numeral(n) => write!(f, "{n}"),
            Constant::Real(n) => write!(f, "{n}.0"),
            Constant::Boolean(b) => write!(f, "{b}"),
            Constant::String(s) => write!(f, "{}", s.display()),
            Constant::BitVec(i, sz) => {
                if sz.is_multiple_of(4) {
                    write!(f, "(lit \"#x{i:00$x}\" (BitVec Size{sz}))", (sz / 4) as usize)
                } else {
                    write!(f, "(lit \"#b{i:00$x}\" (BitVec Size{sz}))", *sz as usize)
                }
            }
        }
    }
}

impl<T: Types> fmt::Display for Qualifier<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(qualif {} ({}) ({}))",
            self.name,
            self.args.iter().format_with(" ", |(name, sort), f| {
                f(&format_args!("({} {sort})", name.display()))
            }),
            self.body
        )
    }
}

impl<T: Types> fmt::Display for FunConstant<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(constant {} (func 0 ({}) {}))",
            self.name.display(),
            self.args
                .iter()
                .format_with(" ", |sort, f| { f(&format_args!("{sort}")) }),
            self.out,
        )?;
        if let Some(comment) = &self.comment {
            write!(f, "  ;; {comment}")?;
        }
        Ok(())
    }
}

impl<T: Types> fmt::Display for FunDef<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let def_kw = if self.recursive { "define" } else { "define_fun" };
        write!(
            f,
            "({def_kw} {} ({}) {} ({}))",
            self.name.display(),
            self.args.iter().format_with(" ", |(name, sort), f| {
                f(&format_args!("({} {sort})", name.display()))
            }),
            self.out,
            self.body
        )?;
        if let Some(comment) = &self.comment {
            write!(f, "  ;; {comment}")?;
        }
        Ok(())
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Mod => write!(f, "mod"),
        }
    }
}

impl fmt::Display for BinRel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinRel::Eq => write!(f, "="),
            BinRel::Ne => write!(f, "!="),
            BinRel::Gt => write!(f, ">"),
            BinRel::Ge => write!(f, ">="),
            BinRel::Lt => write!(f, "<"),
            BinRel::Le => write!(f, "<="),
        }
    }
}

impl fmt::Debug for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
