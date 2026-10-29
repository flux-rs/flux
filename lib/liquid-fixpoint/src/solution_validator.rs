//! Validate a cached concrete assignment using the same SMT encoder as suggestions.
use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    time::Duration,
};

use rustc_data_structures::fx::FxIndexMap;

use crate::{
    parser::{ParseError, StringTypes},
    smt_fmt::{SmtEncoder, SmtOptions},
    *,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ValidationOutcome {
    Valid,
    Rejected,
    Unsupported,
    Inconclusive,
}

type E = Expr<StringTypes>;
type S = Sort<StringTypes>;
type Solution<T> = (Vec<(<T as Types>::Var, Sort<T>)>, Expr<T>);

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

/// Scoped alpha-renaming makes subsequent substitution capture-free. All task
/// locals, parsed solution binders, and globals occupy distinct namespaces.
struct Prepare<'a, T: Types> {
    encoder: SmtEncoder<StringTypes>,
    next: usize,
    globals: HashSet<String>,
    locals: HashMap<String, String>,
    solutions: HashMap<String, Solution<T>>,
    declarations: String,
    reason: &'a mut Option<&'static str>,
}
impl<T: Types> Prepare<'_, T> {
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
                *self.reason = Some("weak_kvar");
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
                    *self.reason = Some("missing_solution");
                    return None;
                };
                if params.len() != args.len() {
                    *self.reason = Some("kvar_arity");
                    return None;
                }
                // Resolve free task locals at this occurrence, while giving lambda
                // parameters their own fresh names before capture-free substitution.
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
                        *self.reason = Some("solution_scope");
                    }
                    return None;
                };
                Some(body.substitute(&subst))
            }
        }
    }
    fn violation(&mut self, c: &Constraint<T>) -> Option<E> {
        match c {
            Constraint::Pred(p, _) => Some(E::Not(Box::new(self.pred(p)?))),
            Constraint::Conj(cs) => {
                Some(E::Or(
                    cs.iter()
                        .map(|c| self.violation(c))
                        .collect::<Option<_>>()?,
                ))
            }
            Constraint::ForAll(b, c) => {
                let saved = self.locals.clone();
                let n = self.fresh();
                let s = sort(&b.sort);
                if !supported_sort(&s, 0) {
                    *self.reason = Some("binder_sort");
                    return None;
                }
                self.encoder
                    .write_const_decl(&mut self.declarations, &n, &s)
                    .ok()?;
                self.locals.insert(b.name.display().to_string(), n);
                let result = (|| {
                    let mut es = b
                        .preds
                        .iter()
                        .map(|p| self.pred(p))
                        .collect::<Option<Vec<_>>>()?;
                    es.push(self.violation(c)?);
                    Some(E::And(es))
                })();
                self.locals = saved;
                result
            }
        }
    }
}

fn supported_sort(s: &S, params: usize) -> bool {
    match s {
        S::Int | S::Bool | S::Real | S::Str => true,
        S::Var(i) => *i < params,
        S::BitVec(s) => matches!(&**s, S::BvSize(n) if *n > 0),
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
        E::App(f, _, es, out) => {
            let head = match &**f {
                E::ThyFunc(ThyFunc::SetEmpty | ThyFunc::MapDefault) => {
                    out.as_ref().is_some_and(|s| supported_sort(s, 0))
                }
                E::Var(_) | E::ThyFunc(_) => true,
                _ => false,
            };
            head && es.iter().all(supported_expr)
        }
    }
}

impl<T: Types> Task<T> {
    /// Parse candidates using the caller's ordinary solution representation and
    /// resolver. Stale or unsupported names must be reported as parse errors.
    pub fn validate_cached_solution_details(
        &self,
        c: &VerificationResult<T::Tag>,
        parse_solution: impl FnMut(&str) -> Result<Solution<T>, ParseError>,
    ) -> (ValidationOutcome, Option<&'static str>) {
        use crate::z3_subprocess::{SatStatus, check_once};
        let query = match self.cached_solution_query(c, parse_solution) {
            Ok(q) => q,
            Err(reason) => return (ValidationOutcome::Unsupported, Some(reason)),
        };
        (
            match check_once(&query, Duration::from_millis(500)) {
                Ok(Some(SatStatus::Unsat)) => ValidationOutcome::Valid,
                Ok(Some(SatStatus::Sat)) => ValidationOutcome::Rejected,
                _ => ValidationOutcome::Inconclusive,
            },
            None,
        )
    }
    fn cached_solution_query(
        &self,
        c: &VerificationResult<T::Tag>,
        mut parse_solution: impl FnMut(&str) -> Result<Solution<T>, ParseError>,
    ) -> Result<String, &'static str> {
        if matches!(c.status, FixpointStatus::Crash(_)) {
            return Err("cached_crash");
        }
        if !matches!(self.solver, SmtSolver::Z3) {
            return Err("solver");
        }
        let data: Vec<DataDecl<StringTypes>> = self
            .data_decls
            .iter()
            .map(|d| {
                DataDecl {
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
            .collect();
        if data.iter().any(|d| {
            d.ctors.is_empty()
                || d.ctors
                    .iter()
                    .any(|c| c.fields.iter().any(|f| !supported_sort(&f.sort, d.vars)))
        }) {
            return Err("datatype_sort");
        }
        let data = crate::constraint_with_env::topo_sort_data_declarations(data);
        let globals: HashSet<_> = self
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
        let mut reason = None;
        let mut p = Prepare {
            encoder: SmtEncoder::new(&data, SmtOptions::VALIDATION),
            next: 0,
            globals,
            locals: HashMap::new(),
            solutions: HashMap::new(),
            declarations: String::new(),
            reason: &mut reason,
        };
        for b in c.solution.iter().chain(&c.non_cuts_solution) {
            let Some(decl) = self
                .kvars
                .iter()
                .find(|k| k.kvid.display().to_string() == b.kvar)
            else {
                continue;
            };
            let solution = parse_solution(&b.val).map_err(|_| "solution_parse")?;
            if solution.0.iter().map(|(_, s)| sort(s)).collect::<Vec<_>>()
                != decl.sorts.iter().map(sort).collect::<Vec<_>>()
            {
                return Err("kvar_sorts");
            }
            if p.solutions.insert(b.kvar.clone(), solution).is_some() {
                return Err("duplicate_solution");
            }
        }
        let violation = p
            .violation(&self.constraint)
            .ok_or(p.reason.unwrap_or("constraint_expression"))?;
        if !supported_expr(&violation) {
            return Err("constraint_expression");
        }
        let mut out = String::from("(set-option :timeout 400)\n");
        for d in &data {
            p.encoder
                .write_datatype_decl(&mut out, d)
                .map_err(|_| "datatype_encoding")?;
        }
        // Emit only referenced globals, closing over function bodies. This also
        // avoids unused synthetic polymorphic comparison declarations.
        let mut used: HashSet<String> = violation.free_vars().into_iter().collect();
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
                    return Err("function_sort");
                }
                output = &ss[1];
            }
            if !supported_sort(output, 0) {
                return Err("polymorphic_function");
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
                return Err("polymorphic_function");
            }
            let inputs: Vec<_> = f.sort.inputs.iter().map(sort).collect();
            let output = sort(&f.sort.output);
            if !inputs.iter().chain([&output]).all(|s| supported_sort(s, 0)) {
                return Err("function_sort");
            }
            let body = if let Some(b) = &f.body {
                let saved = p.locals.clone();
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
                p.locals = saved;
                if !supported_expr(&e) {
                    return Err("function_expression");
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
            let saved = p.locals.clone();
            let bs: Vec<_> = a
                .args
                .iter()
                .map(|(v, s)| {
                    let n = p.fresh();
                    p.locals.insert(v.display().to_string(), n.clone());
                    (n, sort(s))
                })
                .collect();
            let body = p.expr(&a.body).ok_or("axiom_expression")?;
            let e = if bs.is_empty() {
                body
            } else {
                E::Quantifier(Quantifier::Forall, bs, Box::new(body))
            };
            p.locals = saved;
            if !supported_expr(&e) {
                return Err("axiom_expression");
            }
            // Patterns guide instantiation but do not change the axiom's meaning.
            writeln!(out, "(assert {})", p.encoder.expr(&e).map_err(|_| "axiom_encoding")?)
                .unwrap();
        }
        out.push_str(&p.declarations);
        writeln!(
            out,
            "(assert {})\n(check-sat)\n(exit)",
            p.encoder
                .expr(&violation)
                .map_err(|_| "constraint_encoding")?
        )
        .unwrap();
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parser::FromSexp, sexp::Parser};
    type T = StringTypes;

    struct TestNames(usize);
    impl FromSexp<T> for TestNames {
        fn fresh_var(&mut self) -> String {
            let name = format!("parsed_{}", self.0);
            self.0 += 1;
            name
        }
        fn var(&self, name: &str) -> Result<String, ParseError> {
            if matches!(name, "a0" | "a1" | "first" | "ok" | "n") {
                Ok(name.into())
            } else {
                Err(ParseError::err(format!("unknown symbol {name}")))
            }
        }
        fn kvar(&self, _: &str) -> Result<String, ParseError> {
            Err(ParseError::err("unsupported kvar"))
        }
        fn string(&self, s: &str) -> Result<String, ParseError> {
            Ok(s.into())
        }
        fn sort(&self, name: &str) -> Result<String, ParseError> {
            if name == "Pair" { Ok(name.into()) } else { Err(ParseError::err("unknown sort")) }
        }
    }
    fn parser() -> impl FnMut(&str) -> Result<Solution<T>, ParseError> {
        let mut parser = TestNames(0).into_wrapper();
        move |text| {
            let xs = Parser::new(text)
                .parse_all()
                .map_err(ParseError::SexpParseError)?;
            let [s] = xs.as_slice() else {
                return Err(ParseError::err("expected lambda"));
            };
            parser.parse_solution(s)
        }
    }
    impl Task<T> {
        fn validate_cached_solution(&self, c: &VerificationResult<String>) -> bool {
            self.validate_cached_solution_outcome(c) == ValidationOutcome::Valid
        }
        fn validate_cached_solution_outcome(
            &self,
            c: &VerificationResult<String>,
        ) -> ValidationOutcome {
            self.validate_cached_solution_details(c, parser()).0
        }
    }
    fn task() -> Task<T> {
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
    #[test]
    fn initiation_preservation_and_untagged_heads() {
        let t = task();
        assert!(t.validate_cached_solution(&candidate("(>= a 0)")));
        for b in ["false", "true", "(= a 0)"] {
            assert!(!t.validate_cached_solution(&candidate(b)));
        }
        assert!(
            t.validate_cached_solution(&candidate("(exists ((x Int)) (and (= x a) (>= x 0)))"))
        );
        let mut c = candidate("(>= a 0)");
        c.non_cuts_solution = std::mem::take(&mut c.solution);
        assert!(t.validate_cached_solution(&c));
    }
    #[test]
    fn free_task_locals_are_resolved_at_each_occurrence() {
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
        // A returned non-cut definition may refer to a0 outside its lambda.
        let mut c = candidate("(= a a0)");
        assert!(t.validate_cached_solution(&c));
        c.non_cuts_solution = std::mem::take(&mut c.solution);
        assert!(t.validate_cached_solution(&c));

        // Quantifier and lambda binders must not capture the free task local.
        c.non_cuts_solution[0].val =
            "(lambda ((a1 Int)) (exists ((a Int)) (and (= a a1) (= a a0))))".into();
        assert!(t.validate_cached_solution(&c));
        c.non_cuts_solution[0].val = "(lambda ((a0 Int)) (= a0 a0))".into();
        assert_eq!(t.validate_cached_solution_outcome(&c), ValidationOutcome::Rejected);

        c.non_cuts_solution[0].val = "(lambda ((a Int)) (= a a1))".into();
        assert_eq!(
            t.validate_cached_solution_details(&c, parser()),
            (ValidationOutcome::Unsupported, Some("solution_scope"))
        );
        c.non_cuts_solution[0].val = "(lambda ((a Int)) (= a unknown))".into();
        assert_eq!(
            t.validate_cached_solution_details(&c, parser()),
            (ValidationOutcome::Unsupported, Some("solution_parse"))
        );

        c.non_cuts_solution[0].val = "(lambda ((a Bool)) a)".into();
        assert_eq!(
            t.validate_cached_solution_details(&c, parser()),
            (ValidationOutcome::Unsupported, Some("kvar_sorts"))
        );
        // A changed free-local sort is caught by Z3, never accepted as valid.
        c.non_cuts_solution[0].val = "(lambda ((a Int)) (= a a0))".into();
        let Constraint::ForAll(b, _) = &mut t.constraint else { unreachable!() };
        b.sort = S::Str;
        assert_eq!(t.validate_cached_solution_outcome(&c), ValidationOutcome::Inconclusive);
    }
    #[test]
    fn datatype_arguments_and_current_function_definitions() {
        let mut t = task();
        t.data_decls.push(DataDecl {
            name: "Pair".into(),
            vars: 0,
            ctors: vec![DataCtor {
                name: "pair".into(),
                fields: vec![DataField { name: "first".into(), sort: S::Int }],
            }],
        });
        let ds = S::App(SortCtor::Data("Pair".into()), vec![]);
        t.kvars[0].sorts = vec![ds.clone()];
        let app =
            |name: &str, args: Vec<E>| E::App(Box::new(E::Var(name.into())), None, args, None);
        t.constraint = Constraint::ForAll(
            Bind {
                name: "p".into(),
                sort: ds,
                preds: vec![Pred::KVar("k".into(), vec![E::Var("p".into())])],
            },
            Box::new(Constraint::Pred(
                Pred::Expr(app("ok", vec![app("first", vec![E::Var("p".into())])])),
                None,
            )),
        );
        t.define_funs.push(FunDef {
            name: "ok".into(),
            sort: FunSort { params: 0, inputs: vec![S::Int], output: S::Bool },
            body: Some(FunBody {
                args: vec!["n".into()],
                expr: E::Atom(BinRel::Ge, Box::new([E::Var("n".into()), E::int(0)])),
            }),
            comment: None,
        });
        let mut c = candidate("true");
        c.solution[0].val = "(lambda ((a Pair)) (>= (first a) 0))".into();
        assert!(t.validate_cached_solution(&c));
        t.define_funs[0].body.as_mut().unwrap().expr = E::FALSE;
        assert_eq!(t.validate_cached_solution_outcome(&c), ValidationOutcome::Rejected);
    }
    #[test]
    fn current_axioms_are_asserted_and_bad_candidates_fall_back() {
        let mut t = task();
        for val in ["()", "(lambda ((a Bool)) a)", "(lambda ((a Int)) (>= unknown 0))"] {
            let mut c = candidate("true");
            c.solution[0].val = val.into();
            assert!(t.cached_solution_query(&c, parser()).is_err());
        }
        t.constants
            .push(ConstDecl { name: "n".into(), sort: S::Int, comment: None });
        t.constraint = Constraint::Pred(Pred::Expr(E::Var("n".into()).eq(E::int(1))), None);
        t.axioms.push(Axiom {
            name: "one".into(),
            args: vec![],
            body: E::Var("n".into()).eq(E::int(1)),
            patterns: vec![],
        });
        let mut c = candidate("true");
        c.solution.clear();
        assert!(t.validate_cached_solution(&c));
        t.axioms.clear();
        assert_eq!(t.validate_cached_solution_outcome(&c), ValidationOutcome::Rejected);
    }
}
