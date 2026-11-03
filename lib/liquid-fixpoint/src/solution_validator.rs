//! Diagnostic adapter of the validator from commit 786f98aeec.
//! Scoped renaming, complete substitution and current task environment are kept;
//! expose prepared per-clause queries to compare incremental shortcuts.
use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    time::Duration,
};

use rustc_data_structures::fx::FxIndexMap;
use serde::{Deserialize, Serialize};

use crate::{
    parser::StringTypes,
    smt_fmt::{SmtEncoder, SmtOptions},
    *,
};

pub type Solution<T> = (Vec<(<T as Types>::Var, Sort<T>)>, Expr<T>);
type E = Expr<StringTypes>;
type S = Sort<StringTypes>;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Formula {
    pub parameters: Vec<(String, String)>,
    pub body: String,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Clause {
    pub id: usize,
    pub fingerprint: String,
    pub concrete: bool,
    pub formula: Formula,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Prepared {
    pub declarations: String,
    pub clauses: Vec<Clause>,
}

fn sort<T: Types>(s: &Sort<T>) -> S {
    match s {
        Sort::Int => S::Int,
        Sort::Bool => S::Bool,
        Sort::Real => S::Real,
        Sort::Str => S::Str,
        Sort::Var(i) => S::Var(*i),
        Sort::BvSize(i) => S::BvSize(*i),
        Sort::BitVec(s) => S::BitVec(Box::new(sort(s))),
        Sort::Func(ss) => S::Func(Box::new([sort(&ss[0]), sort(&ss[1])])),
        Sort::Abs(i, s) => S::Abs(*i, Box::new(sort(s))),
        Sort::App(c, ss) => {
            S::App(
                match c {
                    SortCtor::Data(n) => SortCtor::Data(n.display().to_string()),
                    SortCtor::Set => SortCtor::Set,
                    SortCtor::Map => SortCtor::Map,
                },
                ss.iter().map(sort).collect(),
            )
        }
    }
}
fn supported_sort(s: &S, params: usize) -> bool {
    match s {
        S::Int | S::Bool | S::Real | S::Str => true,
        S::Var(i) => *i < params,
        S::BitVec(s) => matches!(&**s, S::BvSize(n) if *n > 0),
        // Z3's set syntax differs from the shared formatter. Reject rather than
        // claim success with an approximation.
        S::App(SortCtor::Set, _) => false,
        S::App(_, ss) => ss.iter().all(|s| supported_sort(s, params)),
        _ => false,
    }
}
fn supported_expr(e: &E) -> bool {
    match e {
        E::WKVar(_) => false,
        E::Var(_) | E::Constant(_) => true,
        E::ThyFunc(ThyFunc::SetEmpty | ThyFunc::MapDefault) => false,
        E::ThyFunc(_) => true,
        E::Neg(e) | E::Not(e) | E::IsCtor(_, e) => supported_expr(e),
        E::BinaryOp(_, es) | E::Atom(_, es) | E::Imp(es) | E::Iff(es) | E::Let(_, es) => {
            es.iter().all(supported_expr)
        }
        E::IfThenElse(es) => es.iter().all(supported_expr),
        E::And(es) | E::Or(es) => es.iter().all(supported_expr),
        E::Quantifier(_, bs, e) => {
            bs.iter().all(|(_, s)| supported_sort(s, 0)) && supported_expr(e)
        }
        E::App(f, ss, es, out) => {
            let head = match &**f {
                E::ThyFunc(ThyFunc::SetEmpty | ThyFunc::MapDefault) => {
                    out.as_ref().is_some_and(|s| supported_sort(s, 0))
                }
                E::Var(_) | E::ThyFunc(_) => true,
                _ => false,
            };
            head && ss.as_ref().is_none_or(|ss| ss.is_empty()) && es.iter().all(supported_expr)
        }
    }
}

struct Prepare<T: Types> {
    encoder: SmtEncoder<StringTypes>,
    next: usize,
    globals: HashSet<String>,
    locals: HashMap<String, String>,
    solutions: HashMap<String, Solution<T>>,
    reason: Option<&'static str>,
}
impl<T: Types> Prepare<T> {
    fn fresh(&mut self) -> String {
        loop {
            let n = format!("flux_local_{}", self.next);
            self.next += 1;
            if !self.globals.contains(&n) {
                return n;
            }
        }
    }
    fn expr<U: Types>(&mut self, e: &Expr<U>) -> Option<E> {
        Some(match e {
            Expr::Var(v) => {
                let n = v.display().to_string();
                E::Var(
                    self.locals
                        .get(&n)
                        .cloned()
                        .or_else(|| self.globals.contains(&n).then_some(n))?,
                )
            }
            Expr::Constant(c) => {
                E::Constant(match c {
                    Constant::Numeral(n) => Constant::Numeral(*n),
                    Constant::Boolean(b) => Constant::Boolean(*b),
                    Constant::BitVec(n, s) => Constant::BitVec(*n, *s),
                    Constant::Real(_) | Constant::String(_) => return None,
                })
            }
            Expr::Neg(e) => E::Neg(Box::new(self.expr(e)?)),
            Expr::Not(e) => E::Not(Box::new(self.expr(e)?)),
            Expr::BinaryOp(op, es) => {
                E::BinaryOp(*op, Box::new([self.expr(&es[0])?, self.expr(&es[1])?]))
            }
            Expr::Atom(op, es) => E::Atom(*op, Box::new([self.expr(&es[0])?, self.expr(&es[1])?])),
            Expr::Imp(es) => E::Imp(Box::new([self.expr(&es[0])?, self.expr(&es[1])?])),
            Expr::Iff(es) => E::Iff(Box::new([self.expr(&es[0])?, self.expr(&es[1])?])),
            Expr::And(es) => E::And(es.iter().map(|e| self.expr(e)).collect::<Option<_>>()?),
            Expr::Or(es) => E::Or(es.iter().map(|e| self.expr(e)).collect::<Option<_>>()?),
            Expr::IfThenElse(es) => {
                E::IfThenElse(Box::new([
                    self.expr(&es[0])?,
                    self.expr(&es[1])?,
                    self.expr(&es[2])?,
                ]))
            }
            Expr::ThyFunc(f) => E::ThyFunc(*f),
            Expr::IsCtor(n, e) => E::IsCtor(n.display().to_string(), Box::new(self.expr(e)?)),
            Expr::App(f, ss, es, out) => {
                E::App(
                    Box::new(self.expr(f)?),
                    ss.as_ref().map(|ss| ss.iter().map(sort).collect()),
                    es.iter().map(|e| self.expr(e)).collect::<Option<_>>()?,
                    out.as_ref().map(sort),
                )
            }
            Expr::Quantifier(q, bs, body) => {
                let saved = self.locals.clone();
                let bs = bs
                    .iter()
                    .map(|(n, s)| {
                        let fresh = self.fresh();
                        self.locals.insert(n.display().to_string(), fresh.clone());
                        (fresh, sort(s))
                    })
                    .collect();
                let body = self.expr(body);
                self.locals = saved;
                E::Quantifier(*q, bs, Box::new(body?))
            }
            Expr::Let(n, es) => {
                let value = self.expr(&es[0])?;
                let saved = self.locals.clone();
                let fresh = self.fresh();
                self.locals.insert(n.display().to_string(), fresh.clone());
                let body = self.expr(&es[1]);
                self.locals = saved;
                E::Let(fresh, Box::new([value, body?]))
            }
            Expr::WKVar(_) => {
                self.reason = Some("weak_kvar");
                return None;
            }
        })
    }
    fn pred(&mut self, p: &Pred<T>) -> Option<E> {
        match p {
            Pred::Expr(e) => self.expr(e),
            Pred::KVar(k, args) => {
                let args = args
                    .iter()
                    .map(|e| self.expr(e))
                    .collect::<Option<Vec<_>>>()?;
                let Some((params, body)) = self.solutions.get(&k.display().to_string()).cloned()
                else {
                    self.reason = Some("missing_solution");
                    return None;
                };
                if params.len() != args.len() {
                    self.reason = Some("kvar_arity");
                    return None;
                }
                let saved = self.locals.clone();
                let mut subst = FxIndexMap::default();
                for ((param, _), arg) in params.iter().zip(args) {
                    let fresh = self.fresh();
                    self.locals
                        .insert(param.display().to_string(), fresh.clone());
                    subst.insert(fresh, arg);
                }
                let body = self.expr(&body);
                self.locals = saved;
                let Some(body) = body else {
                    if self.reason.is_none() {
                        self.reason = Some("solution_scope");
                    }
                    return None;
                };
                Some(body.substitute(&subst))
            }
        }
    }
}

impl<T: Types> Task<T> {
    pub fn prepare_solution_clauses(
        &self,
        candidate: &VerificationResult<T::Tag>,
        mut parse: impl FnMut(&str) -> Result<Solution<T>, parser::ParseError>,
    ) -> Result<Prepared, String> {
        if !matches!(self.solver, SmtSolver::Z3) {
            return Err("solver".into());
        }
        let data = self
            .data_decls
            .iter()
            .map(|d| {
                DataDecl::<StringTypes> {
                    name: d.name.display().to_string(),
                    vars: d.vars,
                    ctors: d
                        .ctors
                        .iter()
                        .map(|c| {
                            DataCtor {
                                name: c.name.display().to_string(),
                                fields: c
                                    .fields
                                    .iter()
                                    .map(|f| {
                                        DataField {
                                            name: f.name.display().to_string(),
                                            sort: sort(&f.sort),
                                        }
                                    })
                                    .collect(),
                            }
                        })
                        .collect(),
                }
            })
            .collect::<Vec<_>>();
        if data.iter().any(|d| {
            d.ctors.is_empty()
                || d.ctors
                    .iter()
                    .any(|c| c.fields.iter().any(|f| !supported_sort(&f.sort, d.vars)))
        }) {
            return Err("datatype_sort".into());
        }
        let data = crate::constraint_with_env::topo_sort_data_declarations(data);
        let globals = self
            .constants
            .iter()
            .map(|d| d.name.display().to_string())
            .chain(
                self.define_funs
                    .iter()
                    .map(|f| f.name.display().to_string()),
            )
            .chain(data.iter().flat_map(|d| {
                d.ctors.iter().flat_map(|c| {
                    std::iter::once(c.name.clone()).chain(c.fields.iter().map(|f| f.name.clone()))
                })
            }))
            .collect();
        let mut p = Prepare {
            encoder: SmtEncoder::new(&data, SmtOptions::VALIDATION),
            next: 0,
            globals,
            locals: HashMap::new(),
            solutions: HashMap::new(),
            reason: None,
        };
        for b in candidate
            .solution
            .iter()
            .chain(&candidate.non_cuts_solution)
        {
            let Some(decl) = self
                .kvars
                .iter()
                .find(|k| k.kvid.display().to_string() == b.kvar)
            else {
                continue;
            };
            let solution = parse(&b.val).map_err(|e| format!("solution_parse:{e:?}"))?;
            if solution.0.iter().map(|(_, s)| sort(s)).collect::<Vec<_>>()
                != decl.sorts.iter().map(sort).collect::<Vec<_>>()
            {
                return Err("kvar_sorts".into());
            }
            if p.solutions.insert(b.kvar.clone(), solution).is_some() {
                return Err("duplicate_solution".into());
            }
        }
        let mut clauses = vec![];
        let mut used = HashSet::new();
        for (id, c) in self.constraint.numbered_heads().into_iter().enumerate() {
            p.locals.clear();
            p.next = 0;
            let mut parameters = vec![];
            // Flatten returns binders inner-first; names are otherwise unique.
            for (v, s) in c.binders.iter().rev() {
                let s = sort(s);
                if !supported_sort(&s, 0) {
                    return Err("binder_sort".into());
                }
                let n = p.fresh();
                p.locals.insert(v.display().to_string(), n.clone());
                let mut text = String::new();
                p.encoder
                    .write_sort(&mut text, &s)
                    .map_err(|_| "binder_encoding")?;
                parameters.push((n, text));
            }
            let mut es = c
                .assumptions
                .iter()
                .map(|a| p.pred(a))
                .collect::<Option<Vec<_>>>()
                .ok_or(p.reason.unwrap_or("constraint_expression"))?;
            let head = p
                .pred(&c.head)
                .ok_or(p.reason.unwrap_or("constraint_expression"))?;
            let implication = E::Imp(Box::new([E::And(std::mem::take(&mut es)), head]));
            if !supported_expr(&implication) {
                return Err("constraint_expression".into());
            }
            used.extend(implication.free_vars());
            let body = p
                .encoder
                .expr(&implication)
                .map_err(|_| "constraint_encoding")?;
            // Fingerprint the complete instantiated clause, including assumptions
            // and binder sorts. Keep exact text to avoid trusting hash collisions.
            let fingerprint = serde_json::to_string(&(&parameters, &body)).unwrap();
            clauses.push(Clause {
                id,
                fingerprint,
                concrete: c.head.is_concrete(),
                formula: Formula { parameters, body },
            });
        }
        for a in &self.axioms {
            used.extend(a.body.free_vars().iter().map(|v| v.display().to_string()));
        }
        loop {
            let before = used.len();
            for f in &self.define_funs {
                if used.contains(&f.name.display().to_string())
                    && let Some(b) = &f.body
                {
                    used.extend(b.expr.free_vars().iter().map(|v| v.display().to_string()));
                }
            }
            if before == used.len() {
                break;
            }
        }
        let mut out = String::new();
        for d in &data {
            p.encoder
                .write_datatype_decl(&mut out, d)
                .map_err(|_| "datatype_encoding")?;
        }
        let mut declared = HashSet::new();
        for d in &self.constants {
            let n = d.name.display().to_string();
            if !used.contains(&n) {
                continue;
            }
            let s = sort(&d.sort);
            let mut output = &s;
            while let S::Func(ss) = output {
                if !supported_sort(&ss[0], 0) {
                    return Err("function_sort".into());
                }
                output = &ss[1];
            }
            if !supported_sort(output, 0) {
                return Err("polymorphic_function".into());
            }
            p.encoder
                .write_const_decl(&mut out, &n, &s)
                .map_err(|_| "constant_encoding")?;
            declared.insert(n);
        }
        for f in &self.define_funs {
            let n = f.name.display().to_string();
            if !used.contains(&n) || !declared.insert(n.clone()) {
                continue;
            }
            if f.sort.params != 0 {
                return Err("polymorphic_function".into());
            }
            let inputs = f.sort.inputs.iter().map(sort).collect::<Vec<_>>();
            let output = sort(&f.sort.output);
            if !inputs.iter().chain([&output]).all(|s| supported_sort(s, 0)) {
                return Err("function_sort".into());
            }
            p.locals.clear();
            let body = if let Some(b) = &f.body {
                let args = b
                    .args
                    .iter()
                    .map(|a| {
                        let n = p.fresh();
                        p.locals.insert(a.display().to_string(), n.clone());
                        n
                    })
                    .collect();
                let e = p.expr(&b.expr).ok_or("function_expression")?;
                if !supported_expr(&e) {
                    return Err("function_expression".into());
                }
                Some(FunBody { args, expr: e })
            } else {
                None
            };
            p.encoder
                .write_fun_def(
                    &mut out,
                    &FunDef {
                        name: n,
                        sort: FunSort { params: 0, inputs, output },
                        body,
                        comment: None,
                    },
                )
                .map_err(|_| "function_encoding")?;
        }
        for a in &self.axioms {
            p.locals.clear();
            let bs = a
                .args
                .iter()
                .map(|(v, s)| {
                    let n = p.fresh();
                    p.locals.insert(v.display().to_string(), n.clone());
                    (n, sort(s))
                })
                .collect::<Vec<_>>();
            let body = p.expr(&a.body).ok_or("axiom_expression")?;
            let e = if bs.is_empty() {
                body
            } else {
                E::Quantifier(Quantifier::Forall, bs, Box::new(body))
            };
            if !supported_expr(&e) {
                return Err("axiom_expression".into());
            }
            writeln!(out, "(assert {})", p.encoder.expr(&e).map_err(|_| "axiom_encoding")?)
                .unwrap();
        }
        Ok(Prepared { declarations: out, clauses })
    }
}

/// Encode a typed slot predicate with deterministic formal argument names.
pub fn encode_formula<T: Types>(
    params: &[(T::Var, Sort<T>)],
    body: &Expr<T>,
) -> Result<Formula, String> {
    let mut p = Prepare::<T> {
        encoder: SmtEncoder::new(&[], SmtOptions::VALIDATION),
        next: 0,
        globals: body
            .free_vars()
            .iter()
            .map(|v| v.display().to_string())
            .collect(),
        locals: HashMap::new(),
        solutions: HashMap::new(),
        reason: None,
    };
    let mut parameters = vec![];
    for (i, (v, s)) in params.iter().enumerate() {
        let s = sort(s);
        if !supported_sort(&s, 0) {
            return Err("slot_sort".into());
        }
        let n = format!("flux_arg_{i}");
        p.locals.insert(v.display().to_string(), n.clone());
        let mut text = String::new();
        p.encoder
            .write_sort(&mut text, &s)
            .map_err(|_| "slot_sort_encoding")?;
        parameters.push((n, text));
    }
    let e = p.expr(body).ok_or("slot_expression")?;
    if !supported_expr(&e) {
        return Err("slot_expression".into());
    }
    Ok(Formula { parameters, body: p.encoder.expr(&e).map_err(|_| "slot_encoding")? })
}

/// Bounded fresh process per experiment, with independent scopes per clause.
pub fn check_formulas(
    declarations: &str,
    formulas: &[Formula],
    budget: Duration,
) -> Result<Vec<String>, String> {
    use std::{
        io::Write as _,
        process::{Command, Stdio},
    };

    use process_control::{ChildExt, Control};
    if formulas.is_empty() {
        return Ok(vec![]);
    }
    let mut input = format!("(set-option :timeout {})\n{declarations}\n", budget.as_millis());
    for f in formulas {
        input.push_str("(push)\n");
        for (v, s) in &f.parameters {
            writeln!(input, "(declare-const {v} {s})").unwrap();
        }
        writeln!(input, "(assert (not {}))\n(check-sat)\n(pop)", f.body).unwrap();
    }
    input.push_str("(exit)\n");
    let mut child = Command::new("z3")
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| e.to_string())?;
    let mut stdin = child.stdin.take().ok_or("z3_stdin")?;
    let writer = std::thread::spawn(move || stdin.write_all(input.as_bytes()));
    let output = child
        .controlled_with_output()
        .time_limit(budget)
        .terminate_for_timeout()
        .wait();
    let written = writer.join().map_err(|_| "z3_writer")?;
    let output = output.map_err(|e| e.to_string())?.ok_or("timeout")?;
    written.map_err(|e| e.to_string())?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let statuses = stdout
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>();
    if !output.status.success()
        || !output.stderr.is_empty()
        || statuses.len() != formulas.len()
        || statuses
            .iter()
            .any(|s| !matches!(*s, "sat" | "unsat" | "unknown"))
    {
        return Err(format!("z3_protocol:{stdout}:{}", String::from_utf8_lossy(&output.stderr)));
    }
    Ok(statuses
        .into_iter()
        .map(|s| {
            match s {
                "unsat" => "valid",
                "sat" => "rejected",
                _ => "inconclusive",
            }
            .into()
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        parser::{FromSexp, ParseError},
        sexp::Parser,
    };

    #[test]
    fn canonical_ids_include_empty_conjunction_and_predicate_conjunction() {
        let mut task = task();
        task.constraint = Constraint::Conj(vec![
            Constraint::Conj(vec![]),
            Constraint::Pred(Pred::Expr(E::And(vec![E::TRUE, E::TRUE])), None),
            Constraint::Pred(Pred::KVar("k".into(), vec![E::int(0)]), None),
        ]);
        let candidate = candidate("true");
        let prepared = task.prepare_solution_clauses(&candidate, parse).unwrap();
        assert_eq!(prepared.clauses.iter().map(|c| c.id).collect::<Vec<_>>(), vec![0, 1, 2]);
        assert!(prepared.clauses[0].concrete);
        assert!(!prepared.clauses[2].concrete);
    }

    struct Names(usize);
    impl FromSexp<StringTypes> for Names {
        fn fresh_var(&mut self) -> String {
            let n = self.0;
            self.0 += 1;
            format!("parsed_{n}")
        }
        fn var(&self, name: &str) -> Result<String, ParseError> {
            Ok(name.into())
        }
        fn kvar(&self, name: &str) -> Result<String, ParseError> {
            Ok(name.into())
        }
        fn sort(&self, name: &str) -> Result<String, ParseError> {
            Ok(name.into())
        }
        fn string(&self, name: &str) -> Result<String, ParseError> {
            Ok(name.into())
        }
    }
    fn parse(text: &str) -> Result<Solution<StringTypes>, ParseError> {
        let mut p = Names(0).into_wrapper();
        p.parse_solution(
            &Parser::new(text)
                .parse()
                .map_err(ParseError::SexpParseError)?,
        )
    }
    fn task() -> Task<StringTypes> {
        Task {
            comments: vec![],
            constants: vec![],
            data_decls: vec![],
            define_funs: vec![],
            kvars: vec![KVarDecl::new("k".into(), vec![S::Int], 1)],
            constraint: Constraint::Conj(vec![
                Constraint::Pred(Pred::KVar("k".into(), vec![E::int(0)]), None),
                Constraint::ForAll(
                    Bind {
                        name: "x".into(),
                        sort: S::Int,
                        preds: vec![Pred::KVar("k".into(), vec![E::Var("x".into())])],
                    },
                    Box::new(Constraint::Conj(vec![
                        Constraint::Pred(
                            Pred::KVar(
                                "k".into(),
                                vec![E::BinaryOp(
                                    BinOp::Add,
                                    Box::new([E::Var("x".into()), E::int(1)]),
                                )],
                            ),
                            None,
                        ),
                        Constraint::Pred(
                            Pred::Expr(E::Atom(
                                BinRel::Ge,
                                Box::new([E::Var("x".into()), E::int(0)]),
                            )),
                            None,
                        ),
                    ])),
                ),
            ]),
            qualifiers: vec![],
            axioms: vec![],
            scrape_quals: false,
            solver: SmtSolver::Z3,
        }
    }
    fn candidate(body: &str) -> VerificationResult<String> {
        VerificationResult {
            status: FixpointStatus::Unsafe(Stats::default(), vec![]),
            solution: vec![KVarBind {
                kvar: "k".into(),
                val: format!("(lambda ((a Int)) {body})"),
            }],
            non_cuts_solution: vec![],
            lean_status: LeanStatus::Invalid,
        }
    }
    fn statuses(t: &Task<StringTypes>, c: &VerificationResult<String>) -> Vec<String> {
        let p = t.prepare_solution_clauses(c, parse).unwrap();
        check_formulas(
            &p.declarations,
            &p.clauses
                .iter()
                .map(|c| c.formula.clone())
                .collect::<Vec<_>>(),
            Duration::from_secs(2),
        )
        .unwrap()
    }
    #[test]
    fn checks_initiation_preservation_and_concrete_heads() {
        let t = task();
        assert_eq!(statuses(&t, &candidate("(>= a 0)")), vec!["valid"; 3]);
        // False vacuously validates the concrete head but fails initiation.
        assert_eq!(statuses(&t, &candidate("false")), vec!["rejected", "valid", "valid"]);
        assert_eq!(statuses(&t, &candidate("(= a 0)")), vec!["valid", "rejected", "valid"]);
        let mut c = candidate("(exists ((x Int)) (and (= x a) (>= x 0)))");
        c.non_cuts_solution = std::mem::take(&mut c.solution);
        assert_eq!(statuses(&t, &c), vec!["valid"; 3]);
        c.non_cuts_solution.clear();
        assert!(
            t.prepare_solution_clauses(&c, parse)
                .unwrap_err()
                .contains("missing_solution")
        );
    }
    #[test]
    fn old_candidate_can_fail_when_fresh_candidate_works() {
        let mut t = task();
        let old = candidate("(>= a 0)");
        assert_eq!(statuses(&t, &old), vec!["valid"; 3]);
        let Constraint::Conj(cs) = &mut t.constraint else { unreachable!() };
        cs[0] = Constraint::Pred(Pred::KVar("k".into(), vec![E::int(1)]), None);
        let Constraint::ForAll(_, body) = &mut cs[1] else { unreachable!() };
        let Constraint::Conj(cs) = body.as_mut() else { unreachable!() };
        cs[1] = Constraint::Pred(
            Pred::Expr(E::Atom(BinRel::Ge, Box::new([E::Var("x".into()), E::int(1)]))),
            None,
        );
        assert_eq!(statuses(&t, &old), vec!["valid", "valid", "rejected"]);
        assert_eq!(statuses(&t, &candidate("(>= a 1)")), vec!["valid"; 3]);
    }
    #[test]
    fn scope_capture_sorts_and_bad_parser_inputs() {
        let mut t = task();
        t.constraint = Constraint::ForAll(
            Bind { name: "a0".into(), sort: S::Int, preds: vec![] },
            Box::new(Constraint::Conj(vec![
                Constraint::Pred(Pred::KVar("k".into(), vec![E::Var("a0".into())]), None),
                Constraint::ForAll(
                    Bind {
                        name: "a1".into(),
                        sort: S::Int,
                        preds: vec![Pred::KVar("k".into(), vec![E::Var("a1".into())])],
                    },
                    Box::new(Constraint::Pred(
                        Pred::Expr(E::Var("a1".into()).eq(E::Var("a0".into()))),
                        None,
                    )),
                ),
            ])),
        );
        assert_eq!(statuses(&t, &candidate("(= a a0)")), vec!["valid"; 2]);
        assert_eq!(
            statuses(&t, &candidate("(exists ((a0 Int)) (and (= a0 a) (>= a0 0)))")),
            vec!["rejected", "rejected"]
        );
        assert!(
            t.prepare_solution_clauses(&candidate("(= a a1)"), parse)
                .unwrap_err()
                .contains("solution_scope")
        );
        let mut c = candidate("true");
        c.solution[0].val = "(lambda ((a Bool)) a)".into();
        assert!(
            t.prepare_solution_clauses(&c, parse)
                .unwrap_err()
                .contains("kvar_sorts")
        );
        for text in [
            "()",
            "(lambda ((a Int)) ())",
            "(lambda ((a Int)) 1.2)",
            "(lambda ((a Int)) (+ a))",
            "(lambda ((a Int) (a Int)) a)",
        ] {
            assert!(parse(text).is_err(), "{text}");
        }
    }
    #[test]
    fn current_definitions_and_axioms_are_used() {
        let mut t = task();
        t.kvars.clear();
        t.constants
            .push(ConstDecl { name: "n".into(), sort: S::Int, comment: None });
        t.constraint = Constraint::Pred(
            Pred::Expr(E::App(Box::new(E::Var("ok".into())), None, vec![E::Var("n".into())], None)),
            None,
        );
        t.define_funs.push(FunDef {
            name: "ok".into(),
            sort: FunSort { params: 0, inputs: vec![S::Int], output: S::Bool },
            body: Some(FunBody { args: vec!["x".into()], expr: E::Var("x".into()).eq(E::int(1)) }),
            comment: None,
        });
        t.axioms.push(Axiom {
            name: "one".into(),
            args: vec![],
            body: E::Var("n".into()).eq(E::int(1)),
            patterns: vec![],
        });
        let mut c = candidate("true");
        c.solution.clear();
        assert_eq!(statuses(&t, &c), vec!["valid"]);
        t.axioms.clear();
        assert_eq!(statuses(&t, &c), vec!["rejected"]);
        t.define_funs[0].body.as_mut().unwrap().expr = E::FALSE;
        assert_eq!(statuses(&t, &c), vec!["rejected"]);
    }
    #[test]
    fn implication_directions_protocol_and_budget() {
        let f = |p: &str, q: &str| {
            Formula { parameters: vec![("x".into(), "Int".into())], body: format!("(=> {p} {q})") }
        };
        let fs = vec![f("(>= x 1)", "(>= x 0)"), f("(>= x 0)", "(>= x 1)")];
        assert_eq!(
            check_formulas("", &fs, Duration::from_secs(2)).unwrap(),
            vec!["valid", "rejected"]
        );
        assert!(
            check_formulas(
                "",
                &[Formula { parameters: vec![], body: "unknown_symbol".into() }],
                Duration::from_secs(2)
            )
            .is_err()
        );
        assert!(check_formulas("", &fs, Duration::ZERO).is_err());
    }
}
