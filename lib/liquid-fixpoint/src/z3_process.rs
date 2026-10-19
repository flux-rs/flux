use std::{
    collections::{HashMap, HashSet},
    fmt::Write as _,
    io::{BufRead, BufReader, Read as _, Write as _},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    sync::{Arc, Mutex},
    thread::JoinHandle,
};

use crate::{
    BinOp, BinRel, ConstDecl, Constant, DataDecl, Expr, FlatConstraint, FunDef, Identifier, Pred,
    Sort, Types,
    sexp::{Atom, Parser, Sexp},
    smt_fmt::{SmtEncodeError, SmtEncoder, SmtOptions},
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

impl From<SmtEncodeError> for SuggestionSolverError {
    fn from(err: SmtEncodeError) -> Self {
        match err {
            SmtEncodeError::UnsupportedInput(message) => Self::UnsupportedInput(message),
            SmtEncodeError::Format(err) => Self::Io(err.to_string()),
        }
    }
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

    fn scoped<R>(
        &mut self,
        setup: &str,
        f: impl FnOnce(&mut Self) -> Result<R, SuggestionSolverError>,
    ) -> Result<R, SuggestionSolverError> {
        self.request(&format!("(push)\n{setup}"))?;
        let result = f(self);
        let pop = self.request("(pop)");
        match result {
            Err(err) => Err(err),
            Ok(value) => pop.map(|_| value),
        }
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

pub(crate) struct ProcessSolver<T: Types> {
    session: Z3Session,
    env: ConstraintGlobalEnv<T>,
}

impl<T: Types> ProcessSolver<T> {
    pub(crate) fn new(
        global_consts: &[ConstDecl<T>],
        funs: &[FunDef<T>],
        datatype_decls: &[DataDecl<T>],
    ) -> Result<Self, SuggestionSolverError> {
        let (env, declarations) = ConstraintGlobalEnv::new(datatype_decls, global_consts, funs)?;
        let mut session = Z3Session::new()?;
        session.reset(&declarations)?;
        Ok(Self { session, env })
    }

    pub(crate) fn check_validity(
        &mut self,
        constraint: &FlatConstraint<T>,
    ) -> Result<bool, SuggestionSolverError> {
        let locals = ConstraintLocalEnv::new(&self.env, &[], &constraint.binders)?;
        let mut assertions = constraint
            .preconditions()
            .iter()
            .map(|pred| self.env.pred(pred))
            .collect::<Result<Vec<_>, _>>()?;
        assertions.push(format!("(not {})", self.env.pred(&constraint.head)?));
        let mut query = format!("(push)\n{}", locals.declarations);
        for assertion in &assertions {
            writeln!(query, "(assert {assertion})").unwrap();
        }
        query.push_str("(check-sat)\n(pop)");
        let output = self.session.request(&query)?;
        Ok(matches!(parse_status(&output, &self.session.last_stderr)?, SatStatus::Unsat))
    }

    pub(crate) fn qe_and_simplify(
        &mut self,
        constraint: &FlatConstraint<T>,
        binder_consts: &[ConstDecl<T>],
    ) -> Result<Expr<T>, SuggestionSolverError> {
        let locals = ConstraintLocalEnv::new(&self.env, binder_consts, &constraint.binders)?;
        let assumptions = constraint
            .preconditions()
            .iter()
            .map(|pred| self.env.pred(pred))
            .collect::<Result<Vec<_>, _>>()?;
        let body =
            format!("(=> {} {})", conjunction(&assumptions), self.env.pred(&constraint.head)?);
        let implication = self.env.quantified_implication(constraint, &body)?;
        self.session.scoped(&locals.declarations, |session| {
            Self::qe_and_simplify_in_context(
                session,
                &self.env,
                &locals,
                &assumptions,
                &body,
                &implication,
            )
        })
    }

    fn qe_and_simplify_in_context(
        session: &mut Z3Session,
        env: &ConstraintGlobalEnv<T>,
        locals: &ConstraintLocalEnv<'_, T>,
        assumptions: &[String],
        body: &str,
        implication: &str,
    ) -> Result<Expr<T>, SuggestionSolverError> {
        let query =
            format!("(push)\n(assert {implication})\n(apply (try-for (then qe nnf) 10000))\n(pop)");
        let output = session.request(&query)?;
        let stderr = session.last_stderr.clone();
        if is_timeout(&output) {
            return Err(SuggestionSolverError::QETimeout);
        }
        let goals = parse_goals(&output, &stderr)?;
        let goal = goals.last().ok_or(SuggestionSolverError::NoResults)?;
        let mut candidate = goal
            .iter()
            .map(|formula| locals.decode(formula))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .min_by_key(Expr::total_num_disjuncts)
            .ok_or(SuggestionSolverError::NoResults)?;

        let mut setup = String::new();
        for assumption in assumptions {
            writeln!(setup, "(assert {assumption})").unwrap();
        }
        if session.scoped(&setup, |session| prune_vacuous(&mut candidate, env, session))? {
            return Ok(Expr::FALSE);
        }

        let sanity = format!("(not (=> {} {body}))", env.expr(&candidate)?);
        if matches!(session.check_sat(&[sanity])?, SatStatus::Unsat) {
            Ok(candidate)
        } else {
            Err(SuggestionSolverError::FailedSanityCheck)
        }
    }
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

struct ConstraintGlobalEnv<T: Types> {
    symbols: HashMap<String, T::Var>,
    declared_names: HashSet<String>,
    encoder: SmtEncoder<T>,
}

impl<T: Types> ConstraintGlobalEnv<T> {
    fn new(
        datatype_decls: &[DataDecl<T>],
        global_consts: &[ConstDecl<T>],
        funs: &[FunDef<T>],
    ) -> Result<(Self, String), SuggestionSolverError> {
        let mut symbols = HashMap::new();
        for decl in datatype_decls {
            for ctor in &decl.ctors {
                let name = ctor.name.display().to_string();
                symbols.insert(name, ctor.name.clone());
                for field in &ctor.fields {
                    symbols.insert(field.name.display().to_string(), field.name.clone());
                }
            }
        }
        for decl in global_consts {
            symbols.insert(decl.name.display().to_string(), decl.name.clone());
        }
        for fun in funs {
            symbols.insert(fun.name.display().to_string(), fun.name.clone());
        }
        let encoder = SmtEncoder::new(datatype_decls, SmtOptions::SUGGESTIONS);
        let mut out = String::new();
        for decl in datatype_decls {
            encoder.write_datatype_decl(&mut out, decl)?;
        }

        let mut declared = HashSet::new();
        for decl in global_consts {
            let name = decl.name.display().to_string();
            if declared.insert(name.clone()) {
                encoder.write_const_decl(&mut out, &name, &decl.sort)?;
            }
        }
        for fun in funs {
            let name = fun.name.display().to_string();
            if declared.insert(name.clone()) {
                encoder.write_fun_def(&mut out, fun)?;
            }
        }
        Ok((Self { symbols, declared_names: declared, encoder }, out))
    }

    fn pred(&self, pred: &Pred<T>) -> Result<String, SuggestionSolverError> {
        Ok(self.encoder.pred(pred)?)
    }

    fn expr(&self, expr: &Expr<T>) -> Result<String, SuggestionSolverError> {
        Ok(self.encoder.expr(expr)?)
    }

    fn quantified_implication(
        &self,
        cstr: &FlatConstraint<T>,
        body: &str,
    ) -> Result<String, SuggestionSolverError> {
        let mut quantified = body.to_string();
        for (name, sort) in &cstr.binders {
            let mut binder_sort = String::new();
            self.encoder.write_sort(&mut binder_sort, sort)?;
            quantified = format!("(forall (({} {binder_sort})) {quantified})", name.display());
        }
        Ok(quantified)
    }
}

/// Declarations active in one constraint's solver scope, and names for decoding its result.
struct ConstraintLocalEnv<'a, T: Types> {
    declarations: String,
    symbols: HashMap<String, T::Var>,
    global_symbols: &'a HashMap<String, T::Var>,
}

impl<'a, T: Types> ConstraintLocalEnv<'a, T> {
    fn new(
        globals: &'a ConstraintGlobalEnv<T>,
        binder_consts: &[ConstDecl<T>],
        binders: &[(T::Var, Sort<T>)],
    ) -> Result<Self, SuggestionSolverError> {
        let mut declarations = String::new();
        let mut declared = HashSet::new();
        let mut symbols = HashMap::new();
        for (var, sort) in binder_consts
            .iter()
            .map(|decl| (&decl.name, &decl.sort))
            .chain(binders.iter().map(|(var, sort)| (var, sort)))
        {
            let name = var.display().to_string();
            if !globals.declared_names.contains(&name) && declared.insert(name.clone()) {
                globals
                    .encoder
                    .write_const_decl(&mut declarations, &name, sort)?;
            }
            if !globals.symbols.contains_key(&name) {
                symbols.insert(name, var.clone());
            }
        }
        for (var, _) in binders {
            symbols.insert(var.display().to_string(), var.clone());
        }
        Ok(Self { declarations, symbols, global_symbols: &globals.symbols })
    }

    fn symbol(&self, name: &str) -> Option<&T::Var> {
        self.symbols
            .get(name)
            .or_else(|| self.global_symbols.get(name))
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
                self.symbol(name).cloned().map(Expr::Var).ok_or_else(|| {
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
                let Some(var) = self.symbol(name) else {
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
    env: &ConstraintGlobalEnv<T>,
    session: &mut Z3Session,
) -> Result<bool, SuggestionSolverError> {
    match expr {
        Expr::And(conjuncts) => {
            let copy = conjuncts.clone();
            for (i, conjunct) in conjuncts.iter_mut().enumerate() {
                let mut setup = String::new();
                for (j, sibling) in copy.iter().enumerate() {
                    if i != j {
                        writeln!(setup, "(assert {})", env.expr(sibling)?).unwrap();
                    }
                }
                if session.scoped(&setup, |session| prune_vacuous(conjunct, env, session))? {
                    *expr = Expr::FALSE;
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Expr::Or(disjuncts) => {
            let mut kept = Vec::with_capacity(disjuncts.len());
            for mut disjunct in std::mem::take(disjuncts) {
                if !prune_vacuous(&mut disjunct, env, session)? {
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
        _ => Ok(matches!(session.check_sat(&[env.expr(expr)?])?, SatStatus::Unsat)),
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
