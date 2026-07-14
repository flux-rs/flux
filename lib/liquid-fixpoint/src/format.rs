use std::{
    fmt::{self, Write},
    iter,
};

use itertools::Itertools;

use crate::{
    BinOp, BinRel, ConstDecl, Constant, Constraint, DataCtor, DataDecl, DataField, Expr,
    FixpointFmt, FunDef, FunSort, Identifier, KVarDecl, Qualifier, Sort, SortCtor, Task, Types,
    constraint::{Pred, Quantifier},
};

pub(crate) fn fmt_constraint<T: Types>(
    cstr: &Constraint<T>,
    f: &mut fmt::Formatter<'_>,
    pretty: bool,
) -> fmt::Result {
    let mut cx = ConstraintFormatter::new(pretty);
    write!(f, "(constraint")?;
    cx.incr();
    cx.newline(f)?;
    cx.fmt_constraint(f, cstr)?;
    cx.decr();
    if pretty { writeln!(f, ")") } else { write!(f, ")") }
}

impl<T: Types> fmt::Display for Constraint<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_constraint(self, f, true)
    }
}

pub(crate) fn fmt_task<T: Types>(
    task: &Task<T>,
    f: &mut fmt::Formatter<'_>,
    pretty: bool,
) -> fmt::Result {
    if task.scrape_quals {
        writeln!(f, "(fixpoint \"--scrape=both\")")?;
    }
    if pretty {
        for line in &task.comments {
            writeln!(f, ";; {line}")?;
        }
        writeln!(f)?;
    }

    for data_decl in &task.data_decls {
        writeln!(f, "{data_decl}")?;
    }

    for qualif in &task.qualifiers {
        writeln!(f, "{qualif}")?;
    }

    for cinfo in &task.constants {
        writeln!(f, "{cinfo}")?;
    }

    for fun_decl in &task.define_funs {
        writeln!(f, "{fun_decl}")?;
    }

    for kvar in &task.kvars {
        writeln!(f, "{kvar}")?;
    }

    if pretty {
        writeln!(f)?;
    }
    fmt_constraint(&task.constraint, f, pretty)
}

impl<T: Types> fmt::Display for Task<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_task(self, f, true)
    }
}

pub(crate) struct CompactTask<'a, T: Types>(pub &'a Task<T>);

impl<T: Types> fmt::Display for CompactTask<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_task(self.0, f, false)
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

struct ConstraintFormatter {
    level: u32,
    pretty: bool,
}

impl ConstraintFormatter {
    fn new(pretty: bool) -> Self {
        Self { level: 0, pretty }
    }
    fn fmt_constraint<T: Types>(
        &mut self,
        f: &mut fmt::Formatter<'_>,
        cstr: &Constraint<T>,
    ) -> fmt::Result {
        match cstr {
            Constraint::Pred(head, tag) => {
                if let Some(tag) = tag {
                    write!(f, "(tag {head} \"{tag}\")")
                } else {
                    write!(f, "{head}")
                }
            }
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
                write!(f, "(forall (({} {}) ", bind.name.display(), bind.sort,)?;
                self.fmt_preds_in_assumption_position(&bind.preds, f)?;
                write!(f, ")")?;
                self.incr();
                self.newline(f)?;
                self.fmt_constraint(f, head)?;
                self.decr();
                f.write_str(")")
            }
        }
    }

    fn fmt_preds_in_assumption_position<T: Types>(
        &mut self,
        preds: &[Pred<T>],
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match preds {
            [] => write!(f, "((true))"),
            _ => {
                if preds.len() > 1 {
                    write!(f, "(and")?;
                }
                for (i, pred) in preds.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{pred}")?;
                }
                if preds.len() > 1 {
                    write!(f, ")")?;
                }
                Ok(())
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
        if self.pretty {
            f.write_char('\n')?;
            self.padding(f)
        } else {
            f.write_char(' ')
        }
    }

    fn padding(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.pretty {
            for _ in 0..self.level {
                f.write_str(" ")?;
            }
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
            Pred::KVar(kvid, args) => {
                write!(f, "(${} {})", kvid.display(), args.iter().join(" "),)
            }
            Pred::Expr(expr) => write!(f, "({expr})"),
        }
    }
}

impl fmt::Display for Quantifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Quantifier::Exists => write!(f, "exists"),
            Quantifier::Forall => write!(f, "forall"),
        }
    }
}

impl<T: Types> fmt::Display for Expr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Constant(c) => write!(f, "{c}"),
            Expr::Var(x) => write!(f, "{}", x.display()),
            Expr::App(func, _sort_args, args, _out_sort) => {
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
            Expr::Quantifier(q, sorts, body) => {
                write!(
                    f,
                    "({} ({}) {})",
                    q,
                    sorts.iter().format_with(" ", |(name, sort), f| {
                        f(&format_args!("({} {sort})", name.display()))
                    }),
                    body
                )
            }
        }
    }
}

impl<T: Types> fmt::Display for Constant<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Numeral(n) => write!(f, "{n}"),
            Constant::Real(n) => write!(f, "{}", n.display()),
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

impl<T: Types> fmt::Display for FunDef<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(body) = &self.body {
            write!(
                f,
                "(define_fun {} ({}) {} ({}))",
                self.name.display(),
                iter::zip(&body.args, &self.sort.inputs).format_with(" ", |(name, sort), f| {
                    f(&format_args!("({} {sort})", name.display()))
                }),
                self.sort.output,
                body.expr
            )?;
        } else {
            write!(f, "(constant {} {})", self.name.display(), self.sort)?;
        }
        if let Some(comment) = &self.comment {
            write!(f, "  ;; {comment}")?;
        }
        Ok(())
    }
}

impl<T: Types> fmt::Display for FunSort<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(func {} ({}) {})", self.params, self.inputs.iter().format(" "), self.output)
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
