use std::{
    collections::{HashMap, HashSet},
    fmt::Write as _,
    io::{BufRead, BufReader, Read as _, Write as _},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    sync::{Arc, Mutex},
    thread::JoinHandle,
};

use crate::{
    BinOp, BinRel, ConstDecl, Constant, DataDecl, Expr, FixpointFmt, FlatConstraint, FunDef,
    Identifier, Pred, Quantifier, Sort, SortCtor, ThyFunc, Types,
    sexp::{Atom, Parser, Sexp},
};

#[derive(Debug)]
pub enum SuggestionSolverError {
    Bindings(String),
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

struct Z3Session {
    child: Child,
    stdin: Option<ChildStdin>,
    stdout: BufReader<ChildStdout>,
    stderr: Arc<Mutex<Vec<u8>>>,
    stderr_reader: Option<JoinHandle<()>>,
    last_stderr: String,
    request_id: usize,
}

impl Z3Session {
    fn new() -> Result<Self, SuggestionSolverError> {
        let mut child = Command::new("z3")
            .args(["-smt2", "-in"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|err| SuggestionSolverError::Spawn(err.to_string()))?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| SuggestionSolverError::Io("Z3 stdin was not piped".to_string()))?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| SuggestionSolverError::Io("Z3 stdout was not piped".to_string()))?;
        let mut child_stderr = child
            .stderr
            .take()
            .ok_or_else(|| SuggestionSolverError::Io("Z3 stderr was not piped".to_string()))?;
        let stderr = Arc::new(Mutex::new(Vec::new()));
        let stderr_buf = Arc::clone(&stderr);
        let stderr_reader = std::thread::spawn(move || {
            let mut chunk = [0; 4096];
            loop {
                match child_stderr.read(&mut chunk) {
                    Ok(0) | Err(_) => break,
                    Ok(len) => stderr_buf.lock().unwrap().extend_from_slice(&chunk[..len]),
                }
            }
        });
        Ok(Self {
            child,
            stdin: Some(stdin),
            stdout: BufReader::new(stdout),
            stderr,
            stderr_reader: Some(stderr_reader),
            last_stderr: String::new(),
            request_id: 0,
        })
    }

    fn request(&mut self, commands: &str) -> Result<String, SuggestionSolverError> {
        let marker = format!("__flux_z3_end_{}__", self.request_id);
        self.request_id += 1;
        self.stderr.lock().unwrap().clear();
        let stdin = self
            .stdin
            .as_mut()
            .ok_or_else(|| SuggestionSolverError::Io("Z3 stdin is closed".to_string()))?;
        writeln!(stdin, "{commands}").map_err(|err| SuggestionSolverError::Io(err.to_string()))?;
        writeln!(stdin, "(echo \"{marker}\")")
            .map_err(|err| SuggestionSolverError::Io(err.to_string()))?;
        stdin
            .flush()
            .map_err(|err| SuggestionSolverError::Io(err.to_string()))?;

        let mut response = String::new();
        loop {
            let mut line = String::new();
            let read = self
                .stdout
                .read_line(&mut line)
                .map_err(|err| SuggestionSolverError::Io(err.to_string()))?;
            if read == 0 {
                let status = self
                    .child
                    .try_wait()
                    .map_err(|err| SuggestionSolverError::Io(err.to_string()))?
                    .and_then(|status| status.code());
                self.last_stderr = self.take_stderr();
                return Err(SuggestionSolverError::MalformedResponse {
                    message: format!(
                        "Z3 closed stdout before the response marker (status {status:?})"
                    ),
                    stdout: response,
                    stderr: self.last_stderr.clone(),
                });
            }
            if line.trim() == marker {
                self.last_stderr = self.take_stderr();
                return Ok(response);
            }
            response.push_str(&line);
        }
    }

    fn check_sat(&mut self, assertions: &[String]) -> Result<SatStatus, SuggestionSolverError> {
        let mut commands = String::from("(push)\n");
        for assertion in assertions {
            writeln!(commands, "(assert {assertion})").unwrap();
        }
        commands.push_str("(check-sat)\n(pop)");
        let stdout = self.request(&commands)?;
        parse_status(&stdout, &self.last_stderr)
    }

    fn reset(&mut self, declarations: &str) -> Result<(), SuggestionSolverError> {
        self.request(&format!("(reset)\n{declarations}"))?;
        Ok(())
    }

    fn take_stderr(&self) -> String {
        let bytes = std::mem::take(&mut *self.stderr.lock().unwrap());
        String::from_utf8_lossy(&bytes).into_owned()
    }
}

pub(crate) struct ProcessSolver {
    session: Z3Session,
    last_query: Option<String>,
    context_declarations: Option<String>,
}

impl ProcessSolver {
    pub(crate) fn new(track_queries: bool) -> Result<Self, SuggestionSolverError> {
        Ok(Self {
            session: Z3Session::new()?,
            last_query: track_queries.then(String::new),
            context_declarations: None,
        })
    }

    pub(crate) fn last_query(&self) -> &str {
        self.last_query.as_deref().unwrap_or_default()
    }

    pub(crate) fn initialize_context<T: Types>(
        &mut self,
        global_consts: &[ConstDecl<T>],
        funs: &[FunDef<T>],
        datatype_decls: &[DataDecl<T>],
    ) -> Result<(), SuggestionSolverError> {
        let env = SmtEnv::new(datatype_decls, &[], global_consts, funs, &[]);
        let declarations = env.global_declarations()?;
        self.session.reset(&declarations)?;
        if self.last_query.is_some() {
            self.context_declarations = Some(declarations.clone());
        }
        if let Some(last_query) = &mut self.last_query {
            *last_query = format!("(reset)\n{declarations}");
        }
        Ok(())
    }

    pub(crate) fn check_validity<T: Types>(
        &mut self,
        constraint: &FlatConstraint<T>,
        binder_consts: &[ConstDecl<T>],
        global_consts: &[ConstDecl<T>],
        funs: &[FunDef<T>],
        datatype_decls: &[DataDecl<T>],
    ) -> Result<bool, SuggestionSolverError> {
        if let Some(last_query) = &mut self.last_query {
            last_query.clear();
        }
        let env =
            SmtEnv::new(datatype_decls, binder_consts, global_consts, funs, &constraint.binders);
        let local_declarations = env.local_declarations()?;
        if let Some(last_query) = &mut self.last_query {
            *last_query =
                format!("(reset)\n{}", self.context_declarations.as_deref().unwrap_or_default());
        }
        let mut assertions = constraint
            .preconditions()
            .iter()
            .map(|pred| env.pred(pred))
            .collect::<Result<Vec<_>, _>>()?;
        assertions.push(format!("(not {})", env.pred(&constraint.head)?));
        let mut query = format!("(push)\n{local_declarations}(push)\n");
        for assertion in &assertions {
            writeln!(query, "(assert {assertion})").unwrap();
        }
        query.push_str("(check-sat)\n(pop)\n(pop)");
        if let Some(last_query) = &mut self.last_query {
            last_query.push_str(&format!("(push)\n{local_declarations}(push)\n"));
            for assertion in &assertions {
                last_query.push_str(&format!("(assert {assertion})\n"));
            }
            last_query.push_str("(check-sat)\n(pop)\n(pop)\n");
        }
        let output = self.session.request(&query)?;
        Ok(matches!(parse_status(&output, &self.session.last_stderr)?, SatStatus::Unsat))
    }

    pub(crate) fn qe_and_simplify<T: Types>(
        &mut self,
        constraint: &FlatConstraint<T>,
        binder_consts: &[ConstDecl<T>],
        global_consts: &[ConstDecl<T>],
        funs: &[FunDef<T>],
        datatype_decls: &[DataDecl<T>],
    ) -> Result<Expr<T>, SuggestionSolverError> {
        if let Some(last_query) = &mut self.last_query {
            last_query.clear();
        }
        let env =
            SmtEnv::new(datatype_decls, binder_consts, global_consts, funs, &constraint.binders);
        let local_declarations = env.local_declarations()?;
        if let Some(last_query) = &mut self.last_query {
            *last_query =
                format!("(reset)\n{}", self.context_declarations.as_deref().unwrap_or_default());
        }
        let result = self.qe_and_simplify_in_context(constraint, &env, &local_declarations);
        let pop_result = self.session.request("(pop)");
        if let Some(last_query) = &mut self.last_query {
            last_query.push_str("\n(pop)\n");
        }
        match (result, pop_result) {
            (Err(err), _) => Err(err),
            (Ok(_), Err(err)) => Err(err),
            (Ok(candidate), Ok(_)) => Ok(candidate),
        }
    }

    fn qe_and_simplify_in_context<T: Types>(
        &mut self,
        constraint: &FlatConstraint<T>,
        env: &SmtEnv<'_, T>,
        local_declarations: &str,
    ) -> Result<Expr<T>, SuggestionSolverError> {
        let implication = env.quantified_implication(constraint)?;
        let query = format!(
            "(push)\n{local_declarations}(push)\n(assert {implication})\n(apply (try-for (then qe nnf) 10000))\n(pop)"
        );
        if let Some(last_query) = &mut self.last_query {
            last_query.push_str(&query);
        }
        let output = self.session.request(&query)?;
        let stderr = self.session.last_stderr.clone();
        if is_timeout(&output) {
            return Err(SuggestionSolverError::QETimeout);
        }
        let goals = parse_goals(&output, &stderr)?;
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
        if prune_vacuous(&mut candidate, &env, &base, &[], &mut self.session)? {
            return Ok(Expr::FALSE);
        }

        let sanity =
            format!("(not (=> {} {}))", env.expr(&candidate)?, env.implication_body(constraint)?);
        if matches!(self.session.check_sat(&[sanity])?, SatStatus::Unsat) {
            Ok(candidate)
        } else {
            Err(SuggestionSolverError::FailedSanityCheck)
        }
    }
}

pub(crate) fn equivalent<T: Types>(
    solver: &mut ProcessSolver,
    lhs: &Expr<T>,
    rhs: &Expr<T>,
    constraint: &FlatConstraint<T>,
    binder_consts: &[ConstDecl<T>],
    global_consts: &[ConstDecl<T>],
    funs: &[FunDef<T>],
    datatype_decls: &[DataDecl<T>],
) -> Result<bool, SuggestionSolverError> {
    let env = SmtEnv::new(datatype_decls, binder_consts, global_consts, funs, &constraint.binders);
    let local_declarations = env.local_declarations()?;
    let assumptions = constraint
        .preconditions()
        .iter()
        .map(|pred| env.pred(pred))
        .collect::<Result<Vec<_>, _>>()?;
    let assertion = format!("(not (= {} {}))", env.expr(lhs)?, env.expr(rhs)?);
    let mut query = format!("(push)\n{local_declarations}(push)\n");
    for assumption in &assumptions {
        writeln!(query, "(assert {assumption})").unwrap();
    }
    writeln!(query, "(assert {assertion})\n(check-sat)\n(pop)\n(pop)").unwrap();
    if let Some(last_query) = &mut solver.last_query {
        last_query.push_str(&format!("\n; semantic equivalence check\n{query}"));
    }
    let output = solver.session.request(&query)?;
    Ok(matches!(parse_status(&output, &solver.session.last_stderr)?, SatStatus::Unsat))
}

impl Drop for Z3Session {
    fn drop(&mut self) {
        self.stdin.take();
        let _ = self.child.wait();
        if let Some(reader) = self.stderr_reader.take() {
            let _ = reader.join();
        }
    }
}

struct SmtEnv<'a, T: Types> {
    datatype_decls: &'a [DataDecl<T>],
    binder_consts: &'a [ConstDecl<T>],
    global_consts: &'a [ConstDecl<T>],
    funs: &'a [FunDef<T>],
    binders: &'a [(T::Var, Sort<T>)],
    symbols: HashMap<String, T::Var>,
    constructors: HashSet<String>,
}

impl<'a, T: Types> SmtEnv<'a, T> {
    fn new(
        datatype_decls: &'a [DataDecl<T>],
        binder_consts: &'a [ConstDecl<T>],
        global_consts: &'a [ConstDecl<T>],
        funs: &'a [FunDef<T>],
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
        for fun in funs {
            symbols.insert(fun.name.display().to_string(), fun.name.clone());
        }
        for (name, _) in binders {
            symbols.insert(name.display().to_string(), name.clone());
        }
        Self { datatype_decls, binder_consts, global_consts, funs, binders, symbols, constructors }
    }

    fn global_declarations(&self) -> Result<String, SuggestionSolverError> {
        let mut out = String::new();
        for decl in self.datatype_decls {
            self.write_datatype_decl(&mut out, decl)?;
        }

        let mut declared = HashSet::new();
        for decl in self.global_consts {
            let name = decl.name.display().to_string();
            if declared.insert(name.clone()) {
                self.write_const_decl(&mut out, &name, &decl.sort)?;
            }
        }
        // Function bodies are ignored here, matching the bindings backend.
        for fun in self.funs {
            let name = fun.name.display().to_string();
            if declared.insert(name.clone()) {
                self.write_const_decl(&mut out, &name, &fun.sort.to_sort())?;
            }
        }
        Ok(out)
    }

    fn local_declarations(&self) -> Result<String, SuggestionSolverError> {
        let mut out = String::new();
        let mut declared: HashSet<String> = self
            .global_consts
            .iter()
            .map(|decl| decl.name.display().to_string())
            .chain(self.funs.iter().map(|fun| fun.name.display().to_string()))
            .collect();
        for decl in self.binder_consts {
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

fn prune_vacuous<T: Types>(
    expr: &mut Expr<T>,
    env: &SmtEnv<'_, T>,
    base: &[String],
    siblings: &[Expr<T>],
    session: &mut Z3Session,
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
                        .map(|(_, expr)| expr.clone()),
                );
                if prune_vacuous(conjunct, env, base, &nested, session)? {
                    *expr = Expr::FALSE;
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Expr::Or(disjuncts) => {
            let mut kept = Vec::with_capacity(disjuncts.len());
            for mut disjunct in std::mem::take(disjuncts) {
                if !prune_vacuous(&mut disjunct, env, base, siblings, session)? {
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
            let mut assertions = base.to_vec();
            for sibling in siblings {
                assertions.push(env.expr(sibling)?);
            }
            assertions.push(env.expr(expr)?);
            Ok(matches!(session.check_sat(&assertions)?, SatStatus::Unsat))
        }
    }
}

fn parse_status(stdout: &str, stderr: &str) -> Result<SatStatus, SuggestionSolverError> {
    match stdout.trim() {
        "sat" => Ok(SatStatus::Sat),
        "unsat" => Ok(SatStatus::Unsat),
        "unknown" => Ok(SatStatus::Unknown),
        _ if is_timeout(stdout) => Err(SuggestionSolverError::QETimeout),
        _ => {
            Err(SuggestionSolverError::UnexpectedStatus {
                stdout: stdout.to_string(),
                stderr: stderr.to_string(),
            })
        }
    }
}

fn is_timeout(stdout: &str) -> bool {
    let output = stdout.to_ascii_lowercase();
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
        assert!(is_timeout("(error \"canceled\")"));
        assert!(!is_timeout("sat"));
    }
}
