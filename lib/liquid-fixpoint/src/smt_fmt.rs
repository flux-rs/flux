//! Shared SMTLIB serialization methods

use std::{
    collections::HashSet,
    fmt::{self, Write},
};

use crate::{
    BinOp, BinRel, Constant, DataDecl, Expr, FixpointFmt, FunDef, Identifier, Pred, Quantifier,
    Sort, SortCtor, ThyFunc, Types,
};

macro_rules! parens {
    ($out:ident, $body:block) => {{
        $out.write_char('(')?;
        $body;
        $out.write_char(')')
    }};
}

fn sexp_list<W, I, F>(out: &mut W, items: I, mut write_item: F) -> fmt::Result
where
    W: Write,
    I: IntoIterator,
    F: FnMut(&mut W, I::Item) -> fmt::Result,
{
    out.write_char('(')?;
    for (i, item) in items.into_iter().enumerate() {
        if i != 0 {
            out.write_char(' ')?;
        }
        write_item(out, item)?;
    }
    out.write_char(')')
}

#[derive(Clone, Copy, Default)]
pub(crate) enum FunctionEncoding {
    /// Treat functions as... functions.
    #[default]
    FirstOrder,
    /// Turn functions into arrays (what smt_horn did, not sure why)
    ArrayApproximation,
}

#[derive(Clone, Copy)]
pub(crate) enum PredicateEncoding {
    /// Encode KVars as relations and panic on WKVars (in theory if we wanted it
    /// to solve the wkvars, we would encode those as relations too).
    Horn,
    /// Panic on KVars and replace WKVars with true.
    Suggestions,
}

#[derive(Clone, Copy)]
pub(crate) struct SmtOptions {
    pub functions: FunctionEncoding,
    pub predicates: PredicateEncoding,
}

impl SmtOptions {
    pub const HORN: Self = Self {
        functions: FunctionEncoding::ArrayApproximation,
        predicates: PredicateEncoding::Horn,
    };

    pub const SUGGESTIONS: Self = Self {
        functions: FunctionEncoding::FirstOrder,
        predicates: PredicateEncoding::Suggestions,
    };
}

pub(crate) struct SmtEncoder<T: Types> {
    options: SmtOptions,
    constructors: HashSet<T::Var>,
    datatypes: HashSet<T::Sort>,
}

impl<T: Types> SmtEncoder<T> {
    pub fn new(data_decls: &[DataDecl<T>], options: SmtOptions) -> Self {
        let constructors = data_decls
            .iter()
            .flat_map(|decl| decl.ctors.iter().map(|ctor| ctor.name.clone()))
            .collect();
        let datatypes = data_decls.iter().map(|decl| decl.name.clone()).collect();
        Self { options, constructors, datatypes }
    }

    pub fn write_datatype_decl(&self, out: &mut impl Write, decl: &DataDecl<T>) -> fmt::Result {
        let name = decl.name.display();
        assert!(!decl.ctors.is_empty(), "datatype `{name}` has no constructors");

        parens!(out, {
            write!(out, "declare-datatypes (({name} {})) ", decl.vars)?;
            parens!(out, {
                if decl.vars > 0 {
                    parens!(out, {
                        write!(out, "par ")?;
                        sexp_list(out, 0..decl.vars, |out, i| write!(out, "T{i}"))?;
                        out.write_char(' ')?;
                        self.write_datatype_ctors(out, decl)?;
                    })?;
                } else {
                    self.write_datatype_ctors(out, decl)?;
                }
            })?;
        })?;
        writeln!(out)?;
        Ok(())
    }

    fn write_datatype_ctors(&self, out: &mut impl Write, decl: &DataDecl<T>) -> fmt::Result {
        sexp_list(out, &decl.ctors, |out, ctor| {
            parens!(out, {
                write!(out, "{}", ctor.name.display())?;
                for field in &ctor.fields {
                    out.write_char(' ')?;
                    parens!(out, {
                        write!(out, "{} ", field.name.display())?;
                        self.write_sort_in_scope(out, &field.sort, true)?;
                    })?;
                }
            })?;
            Ok(())
        })
    }

    pub fn write_const_decl(
        &self,
        out: &mut impl Write,
        name: &str,
        sort: &Sort<T>,
    ) -> fmt::Result {
        if matches!(self.options.functions, FunctionEncoding::ArrayApproximation) {
            parens!(out, {
                write!(out, "declare-const {name} ")?;
                self.write_sort(out, sort)?;
            })?;
            writeln!(out)?;
            return Ok(());
        }

        let mut inputs = Vec::new();
        let mut output = sort;
        while let Sort::Func(parts) = output {
            inputs.push(&parts[0]);
            output = &parts[1];
        }
        if matches!(output, Sort::Abs(..))
            || inputs.iter().any(|sort| matches!(sort, Sort::Abs(..)))
        {
            panic!("polymorphic function declaration `{name}`");
        }
        if inputs.is_empty() {
            parens!(out, {
                write!(out, "declare-const {name} ")?;
                self.write_sort(out, output)?;
            })?;
            writeln!(out)?;
        } else {
            self.write_fun_signature(out, name, &inputs, output)?;
        }
        Ok(())
    }

    fn write_fun_signature(
        &self,
        out: &mut impl Write,
        name: &str,
        inputs: &[&Sort<T>],
        output: &Sort<T>,
    ) -> fmt::Result {
        parens!(out, {
            write!(out, "declare-fun {name} ")?;
            sexp_list(out, inputs, |out, sort| self.write_sort(out, sort))?;
            out.write_char(' ')?;
            self.write_sort(out, output)?;
        })?;
        writeln!(out)?;
        Ok(())
    }

    pub fn write_fun_def(&self, out: &mut impl Write, fun: &FunDef<T>) -> fmt::Result {
        if fun.sort.params > 0 && matches!(self.options.functions, FunctionEncoding::FirstOrder) {
            panic!("polymorphic function declaration `{}`", fun.name.display());
        }
        if let Some(body) = &fun.body {
            parens!(out, {
                write!(out, "define-fun {} ", fun.name.display())?;
                sexp_list(out, body.args.iter().zip(&fun.sort.inputs), |out, (name, sort)| {
                    parens!(out, {
                        write!(out, "{} ", name.display())?;
                        self.write_sort(out, sort)?;
                    })?;
                    Ok(())
                })?;
                out.write_char(' ')?;
                self.write_sort(out, &fun.sort.output)?;
                out.write_char(' ')?;
                self.write_expr(out, &body.expr)?;
            })?;
            writeln!(out)?;
        } else {
            let inputs = fun.sort.inputs.iter().collect::<Vec<_>>();
            self.write_fun_signature(
                out,
                &fun.name.display().to_string(),
                &inputs,
                &fun.sort.output,
            )?;
        }
        Ok(())
    }

    pub fn write_sort(&self, out: &mut impl Write, sort: &Sort<T>) -> fmt::Result {
        self.write_sort_in_scope(out, sort, false)
    }

    fn write_sort_in_scope(
        &self,
        out: &mut impl Write,
        sort: &Sort<T>,
        in_datatype_params: bool,
    ) -> fmt::Result {
        match sort {
            Sort::Int => out.write_str("Int")?,
            Sort::Bool => out.write_str("Bool")?,
            Sort::Real => out.write_str("Real")?,
            Sort::Str => out.write_str("String")?,
            Sort::BitVec(size) => {
                let Sort::BvSize(size) = &**size else {
                    panic!("non-constant bit-vector width");
                };
                write!(out, "(_ BitVec {size})")?;
            }
            Sort::BvSize(_) => {
                panic!("bit-vector width used as a value sort");
            }
            Sort::Var(i) => {
                write!(out, "T{i}")?;
            }
            Sort::Func(parts)
                if matches!(self.options.functions, FunctionEncoding::ArrayApproximation) =>
            {
                parens!(out, {
                    out.write_str("Array ")?;
                    self.write_sort_in_scope(out, &parts[0], in_datatype_params)?;
                    out.write_char(' ')?;
                    self.write_sort_in_scope(out, &parts[1], in_datatype_params)?;
                })?;
            }
            Sort::Abs(_, inner)
                if matches!(self.options.functions, FunctionEncoding::ArrayApproximation) =>
            {
                self.write_sort_in_scope(out, inner, in_datatype_params)?;
            }
            Sort::Abs(..) | Sort::Func(_) => {
                panic!("higher-rank or function value sort `{sort:?}`");
            }
            // User opaque sorts are referenced but not declared in the Fixpoint task.
            // Match Haskell Fixpoint's fallback: erase the entire application (including
            // type arguments) to Int. This conflates opaque sorts; Flux well-formedness
            // keeps them distinct before encoding. TODO: carry explicit SortDecls and
            // emit declare-sort instead. An empty datatype is not an opaque sort.
            Sort::App(SortCtor::Data(name), _) if !self.datatypes.contains(name) => {
                out.write_str("Int")?;
            }
            Sort::App(ctor, args) => {
                if args.is_empty() {
                    self.write_sort_ctor(out, ctor)?;
                } else {
                    parens!(out, {
                        self.write_sort_ctor(out, ctor)?;
                        for arg in args {
                            out.write_char(' ')?;
                            self.write_sort_in_scope(out, arg, in_datatype_params)?;
                        }
                    })?;
                }
            }
        }
        Ok(())
    }

    fn write_sort_ctor(&self, out: &mut impl Write, ctor: &SortCtor<T>) -> fmt::Result {
        match ctor {
            SortCtor::Set => out.write_str("Set"),
            SortCtor::Map => out.write_str("Array"),
            SortCtor::Data(name) => write!(out, "{}", name.display()),
        }
    }

    pub fn pred(&self, pred: &Pred<T>) -> Result<String, fmt::Error> {
        let mut out = String::new();
        self.write_pred(&mut out, pred)?;
        Ok(out)
    }

    pub fn write_pred(&self, out: &mut impl Write, pred: &Pred<T>) -> fmt::Result {
        match pred {
            Pred::Expr(expr) => self.write_expr(out, expr),
            Pred::KVar(kvar, args) => {
                match self.options.predicates {
                    PredicateEncoding::Horn => {
                        if args.is_empty() {
                            write!(out, "{}", kvar.display())?;
                        } else {
                            parens!(out, {
                                write!(out, "{}", kvar.display())?;
                                for arg in args {
                                    out.write_char(' ')?;
                                    self.write_expr(out, arg)?;
                                }
                            })?;
                        }
                        Ok(())
                    }
                    PredicateEncoding::Suggestions => {
                        panic!("ordinary KVar in suggestion query")
                    }
                }
            }
        }
    }

    pub fn expr(&self, expr: &Expr<T>) -> Result<String, fmt::Error> {
        let mut out = String::new();
        self.write_expr(&mut out, expr)?;
        Ok(out)
    }

    fn write_weak_kvar(&self, out: &mut impl Write) -> fmt::Result {
        match self.options.predicates {
            PredicateEncoding::Suggestions => {
                out.write_str("true")?;
                Ok(())
            }
            PredicateEncoding::Horn => {
                panic!("weak KVar in Horn query")
            }
        }
    }

    pub fn write_expr(&self, out: &mut impl Write, expr: &Expr<T>) -> fmt::Result {
        match expr {
            Expr::Constant(Constant::Numeral(n)) => write!(out, "{n}")?,
            Expr::Constant(Constant::Boolean(b)) => write!(out, "{b}")?,
            Expr::Constant(Constant::Real(n)) => write!(out, "{}", n.display())?,
            Expr::Constant(Constant::String(s)) => write!(out, "{}", s.display())?,
            Expr::Constant(Constant::BitVec(value, size)) => write!(out, "(_ bv{value} {size})")?,
            Expr::Var(var) => write!(out, "{}", var.display())?,
            Expr::WKVar(_) => self.write_weak_kvar(out)?,
            Expr::Neg(inner) => self.write_unary(out, "-", inner)?,
            Expr::Not(inner) => self.write_unary(out, "not", inner)?,
            Expr::BinaryOp(op, args) => {
                let op = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => "div",
                    BinOp::Mod => "mod",
                };
                self.write_binary(out, op, &args[0], &args[1])?;
            }
            Expr::Atom(BinRel::Ne, args) => {
                parens!(out, {
                    out.write_str("not ")?;
                    self.write_binary(out, "=", &args[0], &args[1])?;
                })?;
            }
            Expr::Atom(rel, args) => {
                let op = match rel {
                    BinRel::Eq => "=",
                    BinRel::Gt => ">",
                    BinRel::Ge => ">=",
                    BinRel::Lt => "<",
                    BinRel::Le => "<=",
                    BinRel::Ne => unreachable!(),
                };
                self.write_binary(out, op, &args[0], &args[1])?;
            }
            Expr::Imp(args) => self.write_binary(out, "=>", &args[0], &args[1])?,
            Expr::Iff(args) => self.write_binary(out, "=", &args[0], &args[1])?,
            Expr::And(exprs) => self.write_nary(out, "and", exprs, "true")?,
            Expr::Or(exprs) => self.write_nary(out, "or", exprs, "false")?,
            Expr::IfThenElse(args) => {
                parens!(out, {
                    out.write_str("ite ")?;
                    self.write_expr(out, &args[0])?;
                    out.write_char(' ')?;
                    self.write_expr(out, &args[1])?;
                    out.write_char(' ')?;
                    self.write_expr(out, &args[2])?;
                })?;
            }
            Expr::Let(name, args) => {
                parens!(out, {
                    out.write_str("let ")?;
                    parens!(out, {
                        parens!(out, {
                            write!(out, "{} ", name.display())?;
                            self.write_expr(out, &args[0])?;
                        })?;
                    })?;
                    out.write_char(' ')?;
                    self.write_expr(out, &args[1])?;
                })?;
            }
            Expr::App(fun, _, args, out_sort) => {
                if matches!(&**fun, Expr::WKVar(_)) {
                    return self.write_weak_kvar(out);
                }
                if args.is_empty() {
                    self.write_application_head(out, fun, out_sort.as_ref())?;
                } else {
                    parens!(out, {
                        self.write_application_head(out, fun, out_sort.as_ref())?;
                        for arg in args {
                            out.write_char(' ')?;
                            self.write_expr(out, arg)?;
                        }
                    })?;
                }
            }
            Expr::ThyFunc(func) => self.write_thy_func(out, *func)?,
            Expr::IsCtor(ctor, inner) => {
                parens!(out, {
                    write!(out, "(_ is {}) ", ctor.display())?;
                    self.write_expr(out, inner)?;
                })?;
            }
            Expr::Quantifier(quantifier, bindings, body) => {
                let quantifier = match quantifier {
                    Quantifier::Exists => "exists",
                    Quantifier::Forall => "forall",
                };
                parens!(out, {
                    write!(out, "{quantifier} ")?;
                    sexp_list(out, bindings, |out, (name, sort)| {
                        parens!(out, {
                            write!(out, "{} ", name.display())?;
                            self.write_sort(out, sort)?;
                        })?;
                        Ok(())
                    })?;
                    out.write_char(' ')?;
                    self.write_expr(out, body)?;
                })?;
            }
        }
        Ok(())
    }

    fn write_application_head(
        &self,
        out: &mut impl Write,
        fun: &Expr<T>,
        out_sort: Option<&Sort<T>>,
    ) -> fmt::Result {
        match fun {
            Expr::Var(name) if self.constructors.contains(name) && out_sort.is_some() => {
                parens!(out, {
                    write!(out, "as {} ", name.display())?;
                    self.write_sort(out, out_sort.unwrap())?;
                })?;
            }
            Expr::ThyFunc(ThyFunc::SetEmpty | ThyFunc::MapDefault) => {
                let sort = out_sort.unwrap_or_else(|| {
                    panic!("empty set or constant array without an output sort")
                });
                let name = if matches!(fun, Expr::ThyFunc(ThyFunc::SetEmpty)) {
                    "emptyset"
                } else {
                    "const"
                };
                parens!(out, {
                    write!(out, "as {name} ")?;
                    self.write_sort(out, sort)?;
                })?;
            }
            other => self.write_expr(out, other)?,
        }
        Ok(())
    }

    fn write_unary(&self, out: &mut impl Write, op: &str, expr: &Expr<T>) -> fmt::Result {
        parens!(out, {
            write!(out, "{op} ")?;
            self.write_expr(out, expr)?;
        })?;
        Ok(())
    }

    fn write_binary(
        &self,
        out: &mut impl Write,
        op: &str,
        lhs: &Expr<T>,
        rhs: &Expr<T>,
    ) -> fmt::Result {
        parens!(out, {
            write!(out, "{op} ")?;
            self.write_expr(out, lhs)?;
            out.write_char(' ')?;
            self.write_expr(out, rhs)?;
        })?;
        Ok(())
    }

    fn write_nary(
        &self,
        out: &mut impl Write,
        op: &str,
        exprs: &[Expr<T>],
        empty: &str,
    ) -> fmt::Result {
        if exprs.is_empty() {
            out.write_str(empty)?;
            return Ok(());
        }
        parens!(out, {
            write!(out, "{op}")?;
            for expr in exprs {
                out.write_char(' ')?;
                self.write_expr(out, expr)?;
            }
        })?;
        Ok(())
    }

    fn write_thy_func(&self, out: &mut impl Write, func: ThyFunc) -> fmt::Result {
        let name = match func {
            ThyFunc::StrLen => "str.len",
            ThyFunc::StrConcat => "str.++",
            ThyFunc::StrPrefixOf => "str.prefixof",
            ThyFunc::StrSuffixOf => "str.suffixof",
            ThyFunc::StrContains => "str.contains",
            ThyFunc::BvZeroExtend(size) => {
                write!(out, "(_ zero_extend {size})")?;
                return Ok(());
            }
            ThyFunc::BvSignExtend(size) => {
                write!(out, "(_ sign_extend {size})")?;
                return Ok(());
            }
            ThyFunc::IntToBv8 => "(_ int2bv 8)",
            ThyFunc::IntToBv32 => "(_ int2bv 32)",
            ThyFunc::IntToBv64 => "(_ int2bv 64)",
            ThyFunc::IntToBv128 => "(_ int2bv 128)",
            ThyFunc::Bv8ToInt | ThyFunc::Bv32ToInt | ThyFunc::Bv64ToInt | ThyFunc::Bv128ToInt => {
                "bv2int"
            }
            ThyFunc::BvUle => "bvule",
            ThyFunc::BvSle => "bvsle",
            ThyFunc::BvUge => "bvuge",
            ThyFunc::BvSge => "bvsge",
            ThyFunc::BvUdiv => "bvudiv",
            ThyFunc::BvSdiv => "bvsdiv",
            ThyFunc::BvSrem => "bvsrem",
            ThyFunc::BvUrem => "bvurem",
            ThyFunc::BvLshr => "bvlshr",
            ThyFunc::BvAshr => "bvashr",
            ThyFunc::BvAnd => "bvand",
            ThyFunc::BvOr => "bvor",
            ThyFunc::BvXor => "bvxor",
            ThyFunc::BvNot => "bvnot",
            ThyFunc::BvAdd => "bvadd",
            ThyFunc::BvNeg => "bvneg",
            ThyFunc::BvSub => "bvsub",
            ThyFunc::BvMul => "bvmul",
            ThyFunc::BvShl => "bvshl",
            ThyFunc::BvUgt => "bvugt",
            ThyFunc::BvSgt => "bvsgt",
            ThyFunc::BvUlt => "bvult",
            ThyFunc::BvSlt => "bvslt",
            ThyFunc::SetEmpty => {
                panic!("unqualified empty set");
            }
            ThyFunc::SetSng => "singleton",
            ThyFunc::SetCup => "union",
            ThyFunc::SetCap => "intersection",
            ThyFunc::SetDif => "setminus",
            ThyFunc::SetMem => "member",
            ThyFunc::SetSub => "subset",
            ThyFunc::MapDefault => {
                panic!("unqualified constant array");
            }
            ThyFunc::MapSelect => "select",
            ThyFunc::MapStore => "store",
        };
        out.write_str(name)?;
        Ok(())
    }
}
