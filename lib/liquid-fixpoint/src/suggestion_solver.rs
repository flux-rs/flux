//! Constraint validity checking and quantifier-elimination-based suggestions.

use std::{
    collections::{HashMap, HashSet},
    fmt::Write as _,
    io,
};

use crate::{
    BinOp, BinRel, ConstDecl, Constant, DataDecl, Expr, FlatConstraint, FunDef, Identifier, Pred,
    Sort, Types,
    sexp::{Atom, Sexp},
    smt_fmt::{SmtEncoder, SmtOptions},
    z3_subprocess::{SatStatus, Z3Error, Z3Subprocess},
};

#[derive(Debug)]
pub enum SuggestionSolverError {
    Z3Process(io::Error),
    QETimeout,
    ContainsQuantifier,
    NoResults,
    FailedSanityCheck,
}

impl From<io::Error> for SuggestionSolverError {
    fn from(err: io::Error) -> Self {
        Self::Z3Process(err)
    }
}

impl From<Z3Error> for SuggestionSolverError {
    fn from(err: Z3Error) -> Self {
        match err {
            Z3Error::Io(err) => Self::Z3Process(err),
            Z3Error::Timeout => Self::QETimeout,
        }
    }
}

pub struct SuggestionSolver<T: Types> {
    session: Z3Subprocess,
    env: ConstraintGlobalEnv<T>,
}

impl<T: Types> SuggestionSolver<T> {
    pub fn new(
        global_consts: &[ConstDecl<T>],
        funs: &[FunDef<T>],
        datatype_decls: Vec<DataDecl<T>>,
    ) -> Result<Self, SuggestionSolverError> {
        let datatype_decls =
            crate::constraint_with_env::topo_sort_data_declarations(datatype_decls);
        let (env, declarations) = ConstraintGlobalEnv::new(&datatype_decls, global_consts, funs)?;
        let mut session = Z3Subprocess::new()?;
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
        let mut setup = locals.declarations;
        for assertion in &assertions {
            writeln!(setup, "(assert {assertion})").unwrap();
        }
        Ok(matches!(self.session.check_sat(&setup)?, SatStatus::Unsat))
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
        session: &mut Z3Subprocess,
        env: &ConstraintGlobalEnv<T>,
        locals: &ConstraintLocalEnv<'_, T>,
        assumptions: &[String],
        body: &str,
        implication: &str,
    ) -> Result<Expr<T>, SuggestionSolverError> {
        let goals =
            session.apply(&format!("(assert {implication})"), "(try-for (then qe nnf) 10000)")?;
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
        if matches!(session.check_sat(&format!("(assert {sanity})"))?, SatStatus::Unsat) {
            Ok(candidate)
        } else {
            Err(SuggestionSolverError::FailedSanityCheck)
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
            encoder.write_datatype_decl(&mut out, decl).unwrap();
        }

        let mut declared = HashSet::new();
        for decl in global_consts {
            let name = decl.name.display().to_string();
            if declared.insert(name.clone()) {
                encoder
                    .write_const_decl(&mut out, &name, &decl.sort)
                    .unwrap();
            }
        }
        for fun in funs {
            let name = fun.name.display().to_string();
            if declared.insert(name.clone()) {
                encoder.write_fun_def(&mut out, fun).unwrap();
            }
        }
        Ok((Self { symbols, declared_names: declared, encoder }, out))
    }

    fn pred(&self, pred: &Pred<T>) -> Result<String, SuggestionSolverError> {
        Ok(self.encoder.pred(pred).unwrap())
    }

    fn expr(&self, expr: &Expr<T>) -> Result<String, SuggestionSolverError> {
        Ok(self.encoder.expr(expr).unwrap())
    }

    fn quantified_implication(
        &self,
        cstr: &FlatConstraint<T>,
        body: &str,
    ) -> Result<String, SuggestionSolverError> {
        let mut quantified = body.to_string();
        for (name, sort) in &cstr.binders {
            let mut binder_sort = String::new();
            self.encoder.write_sort(&mut binder_sort, sort).unwrap();
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
                    .write_const_decl(&mut declarations, &name, sort)
                    .unwrap();
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
            Sexp::Atom(atom) => panic!("unsupported atom in Z3 output: `{atom:?}`"),
            Sexp::List(items) => self.decode_application(items),
        }
    }

    fn decode_symbol(&self, name: &str) -> Result<Expr<T>, SuggestionSolverError> {
        match name {
            "true" => Ok(Expr::TRUE),
            "false" => Ok(Expr::FALSE),
            _ => {
                Ok(Expr::Var(
                    self.symbol(name)
                        .cloned()
                        .unwrap_or_else(|| panic!("unknown symbol in Z3 output: `{name}`")),
                ))
            }
        }
    }

    fn decode_application(&self, items: &[Sexp]) -> Result<Expr<T>, SuggestionSolverError> {
        let Some((head, args)) = items.split_first() else {
            panic!("empty application in Z3 output");
        };
        let head = application_head(head);
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
                // FIXME: substitution below is not scope-aware. For example,
                // (let ((x 1)) (let ((x 2)) x)) should decode to 2, but replacing
                // the outer x also rewrites the inner binding to (let ((1 2)) 1).
                // A fix must also preserve simultaneous let bindings: in
                // (let ((x 1)) (let ((x 2) (y x)) y)), y refers to the outer x,
                // so the result is 1, not 2. Decode all RHSs in the outer scope
                // before extending the environment for the body.
                let args = exact_arg(head, args, 2);
                let Sexp::List(bindings) = &args[0] else {
                    panic!("malformed let bindings in Z3 output: {:?}", args[0]);
                };
                let mut substitutions = HashMap::new();
                for binding in bindings {
                    let Sexp::List(binding) = binding else {
                        panic!("malformed let binding in Z3 output: {binding:?}");
                    };
                    let [Sexp::Atom(Atom::S(name)), value] = binding.as_slice() else {
                        panic!("malformed let binding in Z3 output: {binding:?}");
                    };
                    substitutions.insert(name.as_str(), value);
                }
                self.decode(&substitute_sexp(&args[1], &substitutions))
            }
            "and" => Ok(Expr::And(decoded()?)),
            "or" => Ok(Expr::Or(decoded()?)),
            "not" => Ok(Expr::Not(Box::new(self.decode(&exact_arg(head, args, 1)[0])?))),
            "=>" => {
                let args = exact_arg(head, args, 2);
                Ok(Expr::Imp(Box::new([self.decode(&args[0])?, self.decode(&args[1])?])))
            }
            "=" => {
                let args = exact_arg(head, args, 2);
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
                let args = exact_arg(head, args, 2);
                Ok(Expr::Atom(rel, Box::new([self.decode(&args[0])?, self.decode(&args[1])?])))
            }
            "ite" => {
                let args = exact_arg(head, args, 3);
                Ok(Expr::IfThenElse(Box::new([
                    self.decode(&args[0])?,
                    self.decode(&args[1])?,
                    self.decode(&args[2])?,
                ])))
            }
            "-" if args.len() == 1 => Ok(Expr::Neg(Box::new(self.decode(&args[0])?))),
            "+" | "-" | "*" | "div" | "mod" => {
                if args.len() < 2 {
                    panic!(
                        "expected at least two arguments for `{head}` in Z3 output, got {}",
                        args.len()
                    );
                }
                let op = match head {
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    "*" => BinOp::Mul,
                    "div" => BinOp::Div,
                    "mod" => BinOp::Mod,
                    _ => unreachable!(),
                };
                let mut args = decoded()?.into_iter();
                let lhs = args
                    .next()
                    .expect("binary operator has at least two arguments");
                Ok(args.fold(lhs, |lhs, rhs| Expr::BinaryOp(op, Box::new([lhs, rhs]))))
            }
            name => {
                let var = self
                    .symbol(name)
                    .unwrap_or_else(|| panic!("unknown application in Z3 output: `{name}`"));
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
    session: &mut Z3Subprocess,
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
        _ => {
            Ok(matches!(
                session.check_sat(&format!("(assert {})", env.expr(expr)?))?,
                SatStatus::Unsat
            ))
        }
    }
}

fn application_head(head: &Sexp) -> &str {
    if let Sexp::Atom(Atom::S(name)) = head {
        return name;
    }
    if let Sexp::List(items) = head
        && atom_symbol(items.first()) == Some("as")
        && let Some(Sexp::Atom(Atom::S(name))) = items.get(1)
    {
        return name;
    }
    panic!("unsupported application head in Z3 output: `{head:?}`")
}

fn atom_symbol(sexp: Option<&Sexp>) -> Option<&str> {
    match sexp {
        Some(Sexp::Atom(Atom::S(symbol))) => Some(symbol),
        _ => None,
    }
}

fn exact_arg<'a>(operator: &str, args: &'a [Sexp], expected: usize) -> &'a [Sexp] {
    if args.len() == expected {
        args
    } else {
        panic!(
            "unexpected argument count for `{operator}` in Z3 output: expected {expected}, got {}",
            args.len()
        )
    }
}

fn conjunction(assertions: &[String]) -> String {
    match assertions {
        [] => "true".to_string(),
        [only] => only.clone(),
        _ => format!("(and {})", assertions.join(" ")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp::Parser;

    struct TestTypes;

    impl Types for TestTypes {
        type Sort = &'static str;
        type KVar = &'static str;
        type Var = &'static str;
        type String = String;
        type Real = u32;
        type Tag = String;
    }

    #[test]
    fn decode_left_associative_arithmetic() {
        let globals = ConstraintGlobalEnv::<TestTypes>::new(&[], &[], &[])
            .unwrap()
            .0;
        let locals = ConstraintLocalEnv::new(&globals, &[], &[]).unwrap();
        for (input, expected) in [
            ("(- 10 3 2)", "(- (- 10 3) 2)"),
            ("(div 20 2 2)", "(div (div 20 2) 2)"),
            ("(- 10)", "(- 10)"),
            ("(+ 1 2 3)", "(+ (+ 1 2) 3)"),
        ] {
            let sexp = Parser::new(input).parse().unwrap();
            let expr = locals.decode(&sexp).unwrap();
            assert_eq!(globals.expr(&expr).unwrap(), expected);
        }
    }
}
