use std::{
    collections::{HashMap, HashSet},
    fmt::Write as _,
    io::Write as _,
    process::{Command, Stdio},
};

use crate::{
    BinOp, BinRel, ConstDecl, Constant, DataDecl, Expr, FixpointFmt, FlatConstraint, Identifier,
    Pred, Quantifier, Sort, SortCtor, ThyFunc, Types,
    sexp::{Atom, Parser, Sexp},
};

#[derive(Debug)]
pub enum SuggestionSolverError {
    Spawn(String),
    Io(String),
    ProcessFailure { status: Option<i32>, stdout: String, stderr: String, query: String },
    InvalidUtf8(String),
    UnexpectedStatus { stdout: String, stderr: String },
    MalformedResponse { message: String, stdout: String, stderr: String },
    UnsupportedInput(String),
    UnsupportedOutput(String),
    ContainsQuantifier,
    NoResults,
    QETimeout,
    FailedSanityCheck,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SatStatus {
    Sat,
    Unsat,
    Unknown,
}

struct ProcessOutput {
    stdout: String,
    stderr: String,
}

struct SmtEnv<'a, T: Types> {
    datatype_decls: &'a [DataDecl<T>],
    binder_consts: &'a [ConstDecl<T>],
    global_consts: &'a [ConstDecl<T>],
    binders: &'a [(T::Var, Sort<T>)],
    symbols: HashMap<String, T::Var>,
    constructors: HashSet<String>,
}

impl<'a, T: Types> SmtEnv<'a, T> {
    fn new(
        datatype_decls: &'a [DataDecl<T>],
        binder_consts: &'a [ConstDecl<T>],
        global_consts: &'a [ConstDecl<T>],
        binders: &'a [(T::Var, Sort<T>)],
    ) -> Self {
        let mut symbols = HashMap::new();
        let mut constructors = HashSet::new();
        for decl in datatype_decls {
            for ctor in &decl.ctors {
                let name = ctor.name.display().to_string();
                constructors.insert(name.clone());
                symbols.insert(name, ctor.name.clone());
                for field in &ctor.fields {
                    symbols.insert(field.name.display().to_string(), field.name.clone());
                }
            }
        }
        for decl in binder_consts.iter().chain(global_consts) {
            symbols.insert(decl.name.display().to_string(), decl.name.clone());
        }
        for (name, _) in binders {
            symbols.insert(name.display().to_string(), name.clone());
        }
        Self { datatype_decls, binder_consts, global_consts, binders, symbols, constructors }
    }

    fn declarations(&self) -> Result<String, SuggestionSolverError> {
        let mut out = String::new();
        for decl in self.datatype_decls {
            self.write_datatype_decl(&mut out, decl)?;
        }

        let mut declared = HashSet::new();
        for decl in self.global_consts.iter().chain(self.binder_consts) {
            let name = decl.name.display().to_string();
            if declared.insert(name.clone()) {
                self.write_const_decl(&mut out, &name, &decl.sort)?;
            }
        }
        for (name, sort) in self.binders {
            let name = name.display().to_string();
            if declared.insert(name.clone()) {
                self.write_const_decl(&mut out, &name, sort)?;
            }
        }
        Ok(out)
    }

    fn write_datatype_decl(
        &self,
        out: &mut String,
        decl: &DataDecl<T>,
    ) -> Result<(), SuggestionSolverError> {
        let name = decl.name.display();
        if decl.ctors.is_empty() {
            writeln!(out, "(declare-sort {name} {})", decl.vars).unwrap();
            return Ok(());
        }

        write!(out, "(declare-datatypes (({name} {})) (", decl.vars).unwrap();
        if decl.vars > 0 {
            write!(out, "(par (").unwrap();
            for i in 0..decl.vars {
                if i != 0 {
                    out.push(' ');
                }
                write!(out, "T{i}").unwrap();
            }
            write!(out, ") (").unwrap();
        } else {
            out.push('(');
        }
        for (i, ctor) in decl.ctors.iter().enumerate() {
            if i != 0 {
                out.push(' ');
            }
            write!(out, "({}", ctor.name.display()).unwrap();
            for field in &ctor.fields {
                write!(out, " ({} ", field.name.display()).unwrap();
                self.write_sort(out, &field.sort, true)?;
                out.push(')');
            }
            out.push(')');
        }
        if decl.vars > 0 {
            writeln!(out, "))))").unwrap();
        } else {
            writeln!(out, ")))").unwrap();
        }
        Ok(())
    }

    fn write_const_decl(
        &self,
        out: &mut String,
        name: &str,
        sort: &Sort<T>,
    ) -> Result<(), SuggestionSolverError> {
        let mut inputs = Vec::new();
        let mut output = sort;
        while let Sort::Func(parts) = output {
            inputs.push(&parts[0]);
            output = &parts[1];
        }
        if matches!(output, Sort::Abs(..))
            || inputs.iter().any(|sort| matches!(sort, Sort::Abs(..)))
        {
            return Err(SuggestionSolverError::UnsupportedInput(format!(
                "polymorphic function declaration `{name}`"
            )));
        }
        if inputs.is_empty() {
            write!(out, "(declare-const {name} ").unwrap();
            self.write_sort(out, output, false)?;
            writeln!(out, ")").unwrap();
        } else {
            write!(out, "(declare-fun {name} (").unwrap();
            for (i, input) in inputs.iter().enumerate() {
                if i != 0 {
                    out.push(' ');
                }
                self.write_sort(out, input, false)?;
            }
            write!(out, ") ").unwrap();
            self.write_sort(out, output, false)?;
            writeln!(out, ")").unwrap();
        }
        Ok(())
    }

    fn write_sort(
        &self,
        out: &mut String,
        sort: &Sort<T>,
        bound_vars: bool,
    ) -> Result<(), SuggestionSolverError> {
        match sort {
            Sort::Int => out.push_str("Int"),
            Sort::Bool => out.push_str("Bool"),
            Sort::Real => out.push_str("Real"),
            Sort::Str => out.push_str("String"),
            Sort::BitVec(size) => {
                let Sort::BvSize(size) = &**size else {
                    return Err(SuggestionSolverError::UnsupportedInput(
                        "non-constant bit-vector width".to_string(),
                    ));
                };
                write!(out, "(_ BitVec {size})").unwrap();
            }
            Sort::BvSize(_) => {
                return Err(SuggestionSolverError::UnsupportedInput(
                    "bit-vector width used as a value sort".to_string(),
                ));
            }
            Sort::Var(i) if bound_vars => write!(out, "T{i}").unwrap(),
            Sort::Var(_) => out.push_str("Int"),
            Sort::Abs(_, _) | Sort::Func(_) => {
                return Err(SuggestionSolverError::UnsupportedInput(format!(
                    "higher-rank or function value sort `{sort:?}`"
                )));
            }
            Sort::App(ctor, args) => {
                if args.is_empty() {
                    self.write_sort_ctor(out, ctor);
                } else {
                    out.push('(');
                    self.write_sort_ctor(out, ctor);
                    for arg in args {
                        out.push(' ');
                        self.write_sort(out, arg, bound_vars)?;
                    }
                    out.push(')');
                }
            }
        }
        Ok(())
    }

    fn write_sort_ctor(&self, out: &mut String, ctor: &SortCtor<T>) {
        match ctor {
            SortCtor::Set => out.push_str("Set"),
            SortCtor::Map => out.push_str("Array"),
            SortCtor::Data(name) => write!(out, "{}", name.display()).unwrap(),
        }
    }

    fn pred(&self, pred: &Pred<T>) -> Result<String, SuggestionSolverError> {
        match pred {
            Pred::Expr(expr) => self.expr(expr),
            Pred::KVar(..) => {
                Err(SuggestionSolverError::UnsupportedInput(
                    "ordinary KVar in suggestion query".to_string(),
                ))
            }
        }
    }

    fn expr(&self, expr: &Expr<T>) -> Result<String, SuggestionSolverError> {
        let mut out = String::new();
        self.write_expr(&mut out, expr)?;
        Ok(out)
    }

    fn write_expr(&self, out: &mut String, expr: &Expr<T>) -> Result<(), SuggestionSolverError> {
        match expr {
            Expr::Constant(Constant::Numeral(n)) => write!(out, "{n}").unwrap(),
            Expr::Constant(Constant::Boolean(b)) => write!(out, "{b}").unwrap(),
            Expr::Constant(Constant::Real(n)) => write!(out, "{}", n.display()).unwrap(),
            Expr::Constant(Constant::String(s)) => write!(out, "{}", s.display()).unwrap(),
            Expr::Constant(Constant::BitVec(value, size)) => {
                write!(out, "(_ bv{value} {size})").unwrap();
            }
            Expr::Var(var) => write!(out, "{}", var.display()).unwrap(),
            Expr::WKVar(_) => out.push_str("true"),
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
                out.push_str("(not ");
                self.write_binary(out, "=", &args[0], &args[1])?;
                out.push(')');
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
                out.push_str("(ite ");
                self.write_expr(out, &args[0])?;
                out.push(' ');
                self.write_expr(out, &args[1])?;
                out.push(' ');
                self.write_expr(out, &args[2])?;
                out.push(')');
            }
            Expr::Let(name, args) => {
                write!(out, "(let (({} ", name.display()).unwrap();
                self.write_expr(out, &args[0])?;
                out.push_str(")) ");
                self.write_expr(out, &args[1])?;
                out.push(')');
            }
            Expr::App(fun, _, args, out_sort) => {
                if matches!(&**fun, Expr::WKVar(_)) {
                    out.push_str("true");
                    return Ok(());
                }
                if args.is_empty()
                    && let Expr::Var(name) = &**fun
                    && self.constructors.contains(&name.display().to_string())
                    && let Some(out_sort) = out_sort
                {
                    write!(out, "(as {} ", name.display()).unwrap();
                    self.write_sort(out, out_sort, false)?;
                    out.push(')');
                    return Ok(());
                }
                out.push('(');
                match &**fun {
                    Expr::Var(name)
                        if self.constructors.contains(&name.display().to_string())
                            && out_sort.is_some() =>
                    {
                        write!(out, "(as {} ", name.display()).unwrap();
                        self.write_sort(out, out_sort.as_ref().unwrap(), false)?;
                        out.push(')');
                    }
                    Expr::ThyFunc(func) => out.push_str(thy_func_name(*func)?),
                    other => self.write_expr(out, other)?,
                }
                for arg in args {
                    out.push(' ');
                    self.write_expr(out, arg)?;
                }
                out.push(')');
            }
            Expr::ThyFunc(func) => out.push_str(thy_func_name(*func)?),
            Expr::IsCtor(ctor, inner) => {
                write!(out, "((_ is {}) ", ctor.display()).unwrap();
                self.write_expr(out, inner)?;
                out.push(')');
            }
            Expr::Quantifier(quantifier, bindings, body) => {
                let quantifier = match quantifier {
                    Quantifier::Exists => "exists",
                    Quantifier::Forall => "forall",
                };
                write!(out, "({quantifier} (").unwrap();
                for (i, (name, sort)) in bindings.iter().enumerate() {
                    if i != 0 {
                        out.push(' ');
                    }
                    write!(out, "({} ", name.display()).unwrap();
                    self.write_sort(out, sort, false)?;
                    out.push(')');
                }
                out.push_str(") ");
                self.write_expr(out, body)?;
                out.push(')');
            }
        }
        Ok(())
    }

    fn write_unary(
        &self,
        out: &mut String,
        op: &str,
        expr: &Expr<T>,
    ) -> Result<(), SuggestionSolverError> {
        write!(out, "({op} ").unwrap();
        self.write_expr(out, expr)?;
        out.push(')');
        Ok(())
    }

    fn write_binary(
        &self,
        out: &mut String,
        op: &str,
        lhs: &Expr<T>,
        rhs: &Expr<T>,
    ) -> Result<(), SuggestionSolverError> {
        write!(out, "({op} ").unwrap();
        self.write_expr(out, lhs)?;
        out.push(' ');
        self.write_expr(out, rhs)?;
        out.push(')');
        Ok(())
    }

    fn write_nary(
        &self,
        out: &mut String,
        op: &str,
        exprs: &[Expr<T>],
        empty: &str,
    ) -> Result<(), SuggestionSolverError> {
        if exprs.is_empty() {
            out.push_str(empty);
            return Ok(());
        }
        write!(out, "({op}").unwrap();
        for expr in exprs {
            out.push(' ');
            self.write_expr(out, expr)?;
        }
        out.push(')');
        Ok(())
    }

    fn implication_body(&self, cstr: &FlatConstraint<T>) -> Result<String, SuggestionSolverError> {
        let assumptions = cstr
            .preconditions()
            .iter()
            .map(|pred| self.pred(pred))
            .collect::<Result<Vec<_>, _>>()?;
        let lhs = conjunction(&assumptions);
        let rhs = self.pred(&cstr.head)?;
        Ok(format!("(=> {lhs} {rhs})"))
    }

    fn quantified_implication(
        &self,
        cstr: &FlatConstraint<T>,
    ) -> Result<String, SuggestionSolverError> {
        let body = self.implication_body(cstr)?;
        let mut quantified = body;
        for (name, sort) in &cstr.binders {
            let mut binder_sort = String::new();
            self.write_sort(&mut binder_sort, sort, false)?;
            quantified = format!("(forall (({} {binder_sort})) {quantified})", name.display());
        }
        Ok(quantified)
    }

    fn decode(&self, sexp: &Sexp) -> Result<Expr<T>, SuggestionSolverError> {
        match sexp {
            Sexp::Atom(Atom::B(value)) => Ok(Expr::Constant(Constant::Boolean(*value))),
            Sexp::Atom(Atom::I(value)) if *value >= 0 => {
                Ok(Expr::Constant(Constant::Numeral(*value as u128)))
            }
            Sexp::Atom(Atom::I(value)) => {
                Ok(Expr::Neg(Box::new(Expr::Constant(Constant::Numeral(value.unsigned_abs())))))
            }
            Sexp::Atom(Atom::S(name)) => self.decode_symbol(name),
            Sexp::Atom(atom) => {
                Err(SuggestionSolverError::UnsupportedOutput(format!(
                    "unsupported atom `{atom:?}`"
                )))
            }
            Sexp::List(items) => self.decode_application(items),
        }
    }

    fn decode_symbol(&self, name: &str) -> Result<Expr<T>, SuggestionSolverError> {
        match name {
            "true" => Ok(Expr::TRUE),
            "false" => Ok(Expr::FALSE),
            _ => {
                self.symbols
                    .get(name)
                    .cloned()
                    .map(Expr::Var)
                    .ok_or_else(|| {
                        SuggestionSolverError::UnsupportedOutput(format!("unknown symbol `{name}`"))
                    })
            }
        }
    }

    fn decode_application(&self, items: &[Sexp]) -> Result<Expr<T>, SuggestionSolverError> {
        let Some((head, args)) = items.split_first() else {
            return Err(SuggestionSolverError::UnsupportedOutput("empty application".to_string()));
        };
        let head = application_head(head)?;
        if matches!(head, "forall" | "exists") {
            return Err(SuggestionSolverError::ContainsQuantifier);
        }
        let decoded = || {
            args.iter()
                .map(|arg| self.decode(arg))
                .collect::<Result<Vec<_>, _>>()
        };
        match head {
            "let" => {
                let args = exact_arg(head, args, 2)?;
                let Sexp::List(bindings) = &args[0] else {
                    return Err(SuggestionSolverError::UnsupportedOutput(
                        "malformed let bindings".to_string(),
                    ));
                };
                let mut substitutions = HashMap::new();
                for binding in bindings {
                    let Sexp::List(binding) = binding else {
                        return Err(SuggestionSolverError::UnsupportedOutput(
                            "malformed let binding".to_string(),
                        ));
                    };
                    let [Sexp::Atom(Atom::S(name)), value] = binding.as_slice() else {
                        return Err(SuggestionSolverError::UnsupportedOutput(
                            "malformed let binding".to_string(),
                        ));
                    };
                    substitutions.insert(name.as_str(), value);
                }
                self.decode(&substitute_sexp(&args[1], &substitutions))
            }
            "and" => Ok(Expr::And(decoded()?)),
            "or" => Ok(Expr::Or(decoded()?)),
            "not" => Ok(Expr::Not(Box::new(self.decode(&exact_arg(head, args, 1)?[0])?))),
            "=>" => {
                let args = exact_arg(head, args, 2)?;
                Ok(Expr::Imp(Box::new([self.decode(&args[0])?, self.decode(&args[1])?])))
            }
            "=" => {
                let args = exact_arg(head, args, 2)?;
                Ok(Expr::Atom(
                    BinRel::Eq,
                    Box::new([self.decode(&args[0])?, self.decode(&args[1])?]),
                ))
            }
            "<" | "<=" | ">" | ">=" => {
                let rel = match head {
                    "<" => BinRel::Lt,
                    "<=" => BinRel::Le,
                    ">" => BinRel::Gt,
                    ">=" => BinRel::Ge,
                    _ => unreachable!(),
                };
                let args = exact_arg(head, args, 2)?;
                Ok(Expr::Atom(rel, Box::new([self.decode(&args[0])?, self.decode(&args[1])?])))
            }
            "ite" => {
                let args = exact_arg(head, args, 3)?;
                Ok(Expr::IfThenElse(Box::new([
                    self.decode(&args[0])?,
                    self.decode(&args[1])?,
                    self.decode(&args[2])?,
                ])))
            }
            "-" if args.len() == 1 => Ok(Expr::Neg(Box::new(self.decode(&args[0])?))),
            "+" | "-" | "*" | "div" | "mod" => {
                let op = match head {
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    "*" => BinOp::Mul,
                    "div" => BinOp::Div,
                    "mod" => BinOp::Mod,
                    _ => unreachable!(),
                };
                let mut args = decoded()?.into_iter().rev();
                let rhs = args.next().ok_or_else(|| arg_count(head, 0))?;
                let lhs = args.next().ok_or_else(|| arg_count(head, 1))?;
                Ok(args.fold(Expr::BinaryOp(op, Box::new([lhs, rhs])), |rhs, lhs| {
                    Expr::BinaryOp(op, Box::new([lhs, rhs]))
                }))
            }
            name => {
                let Some(var) = self.symbols.get(name) else {
                    return Err(SuggestionSolverError::UnsupportedOutput(format!(
                        "unknown application `{name}`"
                    )));
                };
                Ok(Expr::App(Box::new(Expr::Var(var.clone())), None, decoded()?, None))
            }
        }
    }
}

fn substitute_sexp(sexp: &Sexp, substitutions: &HashMap<&str, &Sexp>) -> Sexp {
    match sexp {
        Sexp::Atom(Atom::S(name)) => {
            substitutions
                .get(name.as_str())
                .copied()
                .unwrap_or(sexp)
                .clone()
        }
        Sexp::Atom(_) => sexp.clone(),
        Sexp::List(items) => {
            Sexp::List(
                items
                    .iter()
                    .map(|item| substitute_sexp(item, substitutions))
                    .collect(),
            )
        }
    }
}

pub(crate) fn check_validity<T: Types>(
    constraint: &FlatConstraint<T>,
    binder_consts: &[ConstDecl<T>],
    global_consts: &[ConstDecl<T>],
    datatype_decls: &[DataDecl<T>],
) -> Result<bool, SuggestionSolverError> {
    let env = SmtEnv::new(datatype_decls, binder_consts, global_consts, &constraint.binders);
    let mut query = env.declarations()?;
    for pred in &constraint.preconditions() {
        writeln!(query, "(assert {})", env.pred(pred)?).unwrap();
    }
    writeln!(query, "(assert (not {}))", env.pred(&constraint.head)?).unwrap();
    query.push_str("(check-sat)\n");
    Ok(matches!(run_status(&query)?, SatStatus::Unsat))
}

pub(crate) fn qe_and_simplify<T: Types>(
    constraint: &FlatConstraint<T>,
    binder_consts: &[ConstDecl<T>],
    global_consts: &[ConstDecl<T>],
    datatype_decls: &[DataDecl<T>],
) -> Result<Expr<T>, SuggestionSolverError> {
    qe_and_simplify_inner(constraint, binder_consts, global_consts, datatype_decls)
}

fn qe_and_simplify_inner<T: Types>(
    constraint: &FlatConstraint<T>,
    binder_consts: &[ConstDecl<T>],
    global_consts: &[ConstDecl<T>],
    datatype_decls: &[DataDecl<T>],
) -> Result<Expr<T>, SuggestionSolverError> {
    let env = SmtEnv::new(datatype_decls, binder_consts, global_consts, &constraint.binders);
    let implication = env.quantified_implication(constraint)?;
    let mut query = env.declarations()?;
    writeln!(query, "(assert {implication})").unwrap();
    query.push_str("(apply (try-for (then qe nnf) 10000))\n");
    let output = run_z3(&query)?;
    if is_timeout(&output.stdout, &output.stderr) {
        return Err(SuggestionSolverError::QETimeout);
    }
    let goals = parse_goals(&output.stdout, &output.stderr)?;
    let goal = goals.last().ok_or(SuggestionSolverError::NoResults)?;
    let mut candidate = goal
        .iter()
        .map(|formula| env.decode(formula))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .min_by_key(Expr::total_num_disjuncts)
        .ok_or(SuggestionSolverError::NoResults)?;

    let base = constraint
        .preconditions()
        .iter()
        .map(|pred| env.pred(pred))
        .collect::<Result<Vec<_>, _>>()?;
    if prune_vacuous(&mut candidate, &env, &base, &[])? {
        return Ok(Expr::FALSE);
    }

    let sanity_implication = env.implication_body(constraint)?;
    let mut sanity = env.declarations()?;
    writeln!(sanity, "(assert (not (=> {} {sanity_implication})))", env.expr(&candidate)?).unwrap();
    sanity.push_str("(check-sat)\n");
    if matches!(run_status(&sanity)?, SatStatus::Unsat) {
        Ok(candidate)
    } else {
        Err(SuggestionSolverError::FailedSanityCheck)
    }
}

fn prune_vacuous<T: Types>(
    expr: &mut Expr<T>,
    env: &SmtEnv<'_, T>,
    base: &[String],
    siblings: &[Expr<T>],
) -> Result<bool, SuggestionSolverError> {
    match expr {
        Expr::And(conjuncts) => {
            let copy = conjuncts.clone();
            for (i, conjunct) in conjuncts.iter_mut().enumerate() {
                let mut nested = siblings.to_vec();
                nested.extend(
                    copy.iter()
                        .enumerate()
                        .filter(|(j, _)| i != *j)
                        .map(|(_, e)| e.clone()),
                );
                if prune_vacuous(conjunct, env, base, &nested)? {
                    *expr = Expr::FALSE;
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Expr::Or(disjuncts) => {
            let mut kept = Vec::with_capacity(disjuncts.len());
            for mut disjunct in std::mem::take(disjuncts) {
                if !prune_vacuous(&mut disjunct, env, base, siblings)? {
                    kept.push(disjunct);
                }
            }
            match kept.len() {
                0 => {
                    *expr = Expr::FALSE;
                    Ok(true)
                }
                1 => {
                    *expr = kept.pop().unwrap();
                    Ok(false)
                }
                _ => {
                    *disjuncts = kept;
                    Ok(false)
                }
            }
        }
        _ => {
            let mut query = env.declarations()?;
            for assertion in base {
                writeln!(query, "(assert {assertion})").unwrap();
            }
            for sibling in siblings {
                writeln!(query, "(assert {})", env.expr(sibling)?).unwrap();
            }
            writeln!(query, "(assert {})", env.expr(expr)?).unwrap();
            query.push_str("(check-sat)\n");
            Ok(matches!(run_status(&query)?, SatStatus::Unsat))
        }
    }
}

fn run_z3(query: &str) -> Result<ProcessOutput, SuggestionSolverError> {
    let mut child = Command::new("z3")
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|err| SuggestionSolverError::Spawn(err.to_string()))?;
    child
        .stdin
        .take()
        .ok_or_else(|| SuggestionSolverError::Io("Z3 stdin was not piped".to_string()))?
        .write_all(query.as_bytes())
        .map_err(|err| SuggestionSolverError::Io(err.to_string()))?;
    let output = child
        .wait_with_output()
        .map_err(|err| SuggestionSolverError::Io(err.to_string()))?;
    let stdout = String::from_utf8(output.stdout)
        .map_err(|err| SuggestionSolverError::InvalidUtf8(err.to_string()))?;
    let stderr = String::from_utf8(output.stderr)
        .map_err(|err| SuggestionSolverError::InvalidUtf8(err.to_string()))?;
    if !output.status.success() {
        if is_timeout(&stdout, &stderr) {
            return Err(SuggestionSolverError::QETimeout);
        }
        return Err(SuggestionSolverError::ProcessFailure {
            status: output.status.code(),
            stdout,
            stderr,
            query: query.to_string(),
        });
    }
    Ok(ProcessOutput { stdout, stderr })
}

fn run_status(query: &str) -> Result<SatStatus, SuggestionSolverError> {
    let output = run_z3(query)?;
    match output.stdout.trim() {
        "sat" => Ok(SatStatus::Sat),
        "unsat" => Ok(SatStatus::Unsat),
        "unknown" => Ok(SatStatus::Unknown),
        _ if is_timeout(&output.stdout, &output.stderr) => Err(SuggestionSolverError::QETimeout),
        _ => {
            Err(SuggestionSolverError::UnexpectedStatus {
                stdout: output.stdout,
                stderr: output.stderr,
            })
        }
    }
}

fn is_timeout(stdout: &str, stderr: &str) -> bool {
    let output = format!("{stdout}\n{stderr}").to_ascii_lowercase();
    output.contains("timeout")
        || output.contains("timed out")
        || output.contains("canceled")
        || output.contains(":precision under")
        || (output.contains("tactic") && output.contains("failed"))
}

fn parse_goals(stdout: &str, stderr: &str) -> Result<Vec<Vec<Sexp>>, SuggestionSolverError> {
    let parsed = Parser::new(stdout).parse_all().map_err(|err| {
        SuggestionSolverError::MalformedResponse {
            message: format!("{err:?}"),
            stdout: stdout.to_string(),
            stderr: stderr.to_string(),
        }
    })?;
    let [Sexp::List(items)] = parsed.as_slice() else {
        return Err(SuggestionSolverError::MalformedResponse {
            message: "expected one `(goals ...)` response".to_string(),
            stdout: stdout.to_string(),
            stderr: stderr.to_string(),
        });
    };
    if atom_symbol(items.first()) != Some("goals") {
        return Err(SuggestionSolverError::MalformedResponse {
            message: "response does not start with `goals`".to_string(),
            stdout: stdout.to_string(),
            stderr: stderr.to_string(),
        });
    }
    items[1..]
        .iter()
        .map(|goal| {
            let Sexp::List(entries) = goal else {
                return Err(SuggestionSolverError::MalformedResponse {
                    message: "goal is not a list".to_string(),
                    stdout: stdout.to_string(),
                    stderr: stderr.to_string(),
                });
            };
            if atom_symbol(entries.first()) != Some("goal") {
                return Err(SuggestionSolverError::MalformedResponse {
                    message: "expected `(goal ...)`".to_string(),
                    stdout: stdout.to_string(),
                    stderr: stderr.to_string(),
                });
            }
            let metadata = entries[1..]
                .iter()
                .position(|entry| {
                    atom_symbol(Some(entry)).is_some_and(|name| name.starts_with(':'))
                })
                .unwrap_or(entries.len() - 1);
            Ok(entries[1..1 + metadata].to_vec())
        })
        .collect()
}

fn application_head(head: &Sexp) -> Result<&str, SuggestionSolverError> {
    if let Sexp::Atom(Atom::S(name)) = head {
        return Ok(name);
    }
    if let Sexp::List(items) = head
        && atom_symbol(items.first()) == Some("as")
        && let Some(Sexp::Atom(Atom::S(name))) = items.get(1)
    {
        return Ok(name);
    }
    Err(SuggestionSolverError::UnsupportedOutput(format!(
        "unsupported application head `{head:?}`"
    )))
}

fn atom_symbol(sexp: Option<&Sexp>) -> Option<&str> {
    match sexp {
        Some(Sexp::Atom(Atom::S(symbol))) => Some(symbol),
        _ => None,
    }
}

fn exact_arg<'a>(
    operator: &str,
    args: &'a [Sexp],
    expected: usize,
) -> Result<&'a [Sexp], SuggestionSolverError> {
    if args.len() == expected { Ok(args) } else { Err(arg_count(operator, args.len())) }
}

fn arg_count(operator: &str, actual: usize) -> SuggestionSolverError {
    SuggestionSolverError::UnsupportedOutput(format!(
        "unexpected argument count for `{operator}`: {actual}"
    ))
}

fn conjunction(assertions: &[String]) -> String {
    match assertions {
        [] => "true".to_string(),
        [only] => only.clone(),
        _ => format!("(and {})", assertions.join(" ")),
    }
}

fn thy_func_name(func: ThyFunc) -> Result<&'static str, SuggestionSolverError> {
    match func {
        ThyFunc::StrLen => Ok("str.len"),
        ThyFunc::StrConcat => Ok("str.++"),
        ThyFunc::StrPrefixOf => Ok("str.prefixof"),
        ThyFunc::StrSuffixOf => Ok("str.suffixof"),
        ThyFunc::StrContains => Ok("str.contains"),
        ThyFunc::MapSelect => Ok("select"),
        ThyFunc::MapStore => Ok("store"),
        other => {
            Err(SuggestionSolverError::UnsupportedInput(format!("theory function `{other:?}`")))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_multiple_goals_and_metadata() {
        let goals = parse_goals(
            "(goals (goal false :precision precise :depth 1) (goal (> x 0) :precision precise))",
            "",
        )
        .unwrap();
        assert_eq!(goals.len(), 2);
        assert_eq!(goals[0], vec![Sexp::Atom(Atom::B(false))]);
        assert_eq!(goals[1].len(), 1);
    }

    #[test]
    fn status_is_exact() {
        assert_eq!(" sat \n".trim(), "sat");
        assert!(is_timeout("(error \"canceled\")", ""));
    }
}
