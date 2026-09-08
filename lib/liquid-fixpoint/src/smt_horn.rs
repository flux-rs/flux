/// Formatter for the SMT-LIB HORN CHC format used by hornspec.
///
/// This format uses `set-logic HORN`, `declare-fun`, `assert (forall ...)`, and `check-sat`.
/// Example:
/// ```smt2
/// (set-logic HORN)
/// (declare-fun P0 (Int) Bool)
/// (declare-fun P1 (Int Int) Bool)
/// (assert (forall ((x Int)) (=> (P0 x) (P1 x x))))
/// (assert (forall ((x Int)) (=> (and (P1 x x) (not (>= x 0))) false)))
/// (check-sat)
/// ```
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use crate::{
    BinOp, BinRel, ConstDecl, Constant, Constraint, DataCtor, DataDecl, Expr, FixpointFmt, FunDef,
    Identifier, KVarDecl, Sort, SortCtor, Task, ThyFunc, Types, constraint::Pred,
};

/// A flattened Horn clause extracted from the constraint tree.
struct HornClause<'a, T: Types> {
    /// Universally quantified variables with their sorts
    vars: Vec<(&'a T::Var, &'a Sort<T>)>,
    /// Guard predicates (body of the implication)
    guards: Vec<&'a Pred<T>>,
    /// Head of the clause
    head: &'a Pred<T>,
}

/// Collect all Horn clauses from a constraint tree
fn flatten_constraint<'a, T: Types>(
    constraint: &'a Constraint<T>,
    vars: &mut Vec<(&'a T::Var, &'a Sort<T>)>,
    guards: &mut Vec<&'a Pred<T>>,
    clauses: &mut Vec<HornClause<'a, T>>,
) {
    match constraint {
        Constraint::ForAll(bind, body) => {
            vars.push((&bind.name, &bind.sort));
            let guard_len = guards.len();
            guards.extend(bind.preds.iter().filter(|a| !a.is_trivially_true()));
            flatten_constraint(body, vars, guards, clauses);
            guards.truncate(guard_len);
            vars.pop();
        }
        Constraint::Conj(cstrs) => {
            for cstr in cstrs {
                flatten_constraint(cstr, vars, guards, clauses);
            }
        }
        Constraint::Pred(head, _tag) => {
            if head.is_trivially_true() {
                return;
            }
            clauses.push(HornClause { vars: vars.clone(), guards: guards.clone(), head });
        }
    }
}

/// Walks the top-level conjuncts of `expr`.
fn for_each_conjunct<'a, T: Types>(expr: &'a Expr<T>, f: &mut impl FnMut(&'a Expr<T>)) {
    match expr {
        Expr::And(exprs) => {
            for expr in exprs {
                for_each_conjunct(expr, f);
            }
        }
        _ => f(expr),
    }
}

/// Collects every variable occurring in `expr`. Variables bound inside `expr` (by a `let` or a
/// quantifier) are collected too, which only makes the callers more conservative.
fn collect_vars<'a, T: Types>(expr: &'a Expr<T>, out: &mut Vec<&'a T::Var>) {
    match expr {
        Expr::Var(var) => out.push(var),
        Expr::Constant(_) | Expr::ThyFunc(_) => {}
        Expr::Neg(expr) | Expr::Not(expr) | Expr::IsCtor(_, expr) => collect_vars(expr, out),
        Expr::BinaryOp(_, exprs) | Expr::Atom(_, exprs) => {
            for expr in exprs.iter() {
                collect_vars(expr, out);
            }
        }
        Expr::Imp(exprs) | Expr::Iff(exprs) => {
            for expr in exprs.iter() {
                collect_vars(expr, out);
            }
        }
        Expr::IfThenElse(exprs) => {
            for expr in exprs.iter() {
                collect_vars(expr, out);
            }
        }
        Expr::And(exprs) | Expr::Or(exprs) => {
            for expr in exprs {
                collect_vars(expr, out);
            }
        }
        Expr::Let(name, exprs) => {
            out.push(name);
            for expr in exprs.iter() {
                collect_vars(expr, out);
            }
        }
        Expr::App(func, _, args, _) => {
            collect_vars(func, out);
            for arg in args {
                collect_vars(arg, out);
            }
        }
        // Both make the formatter bail out on the whole task, so there is nothing to collect.
        Expr::Quantifier(..) | Expr::WKVar(..) => {}
    }
}

/// Finds constants whose value is pinned by a `(= c <term>)` guard, so they can be emitted as an
/// interpreted `define-fun` rather than an uninterpreted `declare-const`.
///
/// This is not cosmetic: spacer's rule language admits only applications of the predicates being
/// solved for plus interpreted constraints, so a rule mentioning an uninterpreted non-`Bool`
/// symbol is rejected outright with `Uninterpreted 'c0'` and the whole query comes back `unknown`.
/// Flux declares Rust constants (`i32::MAX` and friends) this way and pins them with a guard, so
/// the value is known and the symbol need not be uninterpreted at all.
///
/// A definition is only used when the term is closed -- it mentions no variable bound by the
/// clause the guard was found in -- and when every clause that pins the constant pins it to the
/// same term. Constants failing either test stay uninterpreted.
fn find_const_definitions<'a, T: Types>(
    constants: &'a [ConstDecl<T>],
    clauses: &[HornClause<'a, T>],
) -> HashMap<&'a T::Var, &'a Expr<T>> {
    let declared: HashSet<&T::Var> = constants.iter().map(|c| &c.name).collect();
    if declared.is_empty() {
        return HashMap::new();
    }

    // `None` marks a constant seen with two different definitions.
    let mut defs: HashMap<&T::Var, Option<&Expr<T>>> = HashMap::new();
    for clause in clauses {
        let bound: HashSet<&T::Var> = clause.vars.iter().map(|(var, _)| *var).collect();
        for guard in &clause.guards {
            let Pred::Expr(expr) = guard else { continue };
            let mut conjuncts = Vec::new();
            for_each_conjunct(expr, &mut |conj| conjuncts.push(conj));
            for conj in conjuncts {
                let Expr::Atom(BinRel::Eq, exprs) = conj else { continue };
                let [lhs, rhs] = &**exprs;
                // An equation defines a constant read in either direction.
                for (var, term) in [(lhs, rhs), (rhs, lhs)] {
                    let Expr::Var(name) = var else { continue };
                    if !declared.contains(&name) {
                        continue;
                    }
                    let mut vars = Vec::new();
                    collect_vars(term, &mut vars);
                    if vars.iter().any(|var| bound.contains(var) || *var == name) {
                        continue;
                    }
                    defs.entry(name)
                        .and_modify(|slot| {
                            if *slot != Some(term) {
                                *slot = None;
                            }
                        })
                        .or_insert(Some(term));
                }
            }
        }
    }
    defs.into_iter()
        .filter_map(|(name, def)| def.map(|def| (name, def)))
        .collect()
}

// ---- SMT-LIB HORN CHC task formatting ----

/// Format a task in the SMT-LIB HORN CHC format
pub fn fmt_smt_horn<T: Types>(task: &Task<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    // Set logic
    writeln!(f, "(set-logic HORN)")?;
    writeln!(f)?;

    // Comments
    for line in &task.comments {
        writeln!(f, ";; {line}")?;
    }
    if !task.comments.is_empty() {
        writeln!(f)?;
    }

    // Flatten constraints into Horn clauses up front: the clause binders are needed to know which
    // sort variables have to be declared.
    let mut clauses = Vec::new();
    let mut vars = Vec::new();
    let mut guards = Vec::new();
    flatten_constraint(&task.constraint, &mut vars, &mut guards, &mut clauses);

    // Sort variables occurring outside a datatype declaration are declared with z3's
    // `declare-type-var` extension, which makes the declarations genuinely polymorphic: the same
    // symbol can then be used at several instances (e.g. the `gt`/`le` uninterpreted relations
    // applied at both `Int` and `Bool`), which skolemizing them into a single uninterpreted sort
    // would reject.
    let mut max_sort_var = None;
    for sort in task
        .constants
        .iter()
        .map(|c| &c.sort)
        .chain(task.kvars.iter().flat_map(|k| &k.sorts))
        .chain(
            task.define_funs
                .iter()
                .flat_map(|d| d.sort.inputs.iter().chain(std::iter::once(&d.sort.output))),
        )
        .chain(
            clauses
                .iter()
                .flat_map(|c| c.vars.iter().map(|(_, sort)| *sort)),
        )
    {
        max_sort_var_of(sort, &mut max_sort_var);
    }
    if let Some(max) = max_sort_var {
        for i in 0..=max {
            writeln!(f, "(declare-type-var {SORT_VAR_PREFIX}{i})")?;
        }
    }

    // Data type declarations. Sorts without constructors are opaque and must come first, since
    // datatype bodies may refer to them.
    let (opaque, datatypes): (Vec<_>, Vec<_>) = task
        .data_decls
        .iter()
        .partition(|decl| decl.ctors.is_empty());
    let mut declared: HashSet<String> = HashSet::new();
    for decl in opaque {
        writeln!(f, "(declare-sort {} {})", decl.name.display(), decl.vars)?;
        declared.insert(decl.name.display().to_string());
    }

    // Sorts referenced but never declared (e.g. opaque sorts introduced by the encoding) are
    // declared as uninterpreted sorts of the right arity.
    let declared_names: HashSet<String> = task
        .data_decls
        .iter()
        .map(|decl| decl.name.display().to_string())
        .collect();
    let mut undeclared = Vec::new();
    for sort in datatypes
        .iter()
        .flat_map(|decl| &decl.ctors)
        .flat_map(|ctor| &ctor.fields)
        .map(|field| &field.sort)
        .chain(task.constants.iter().map(|c| &c.sort))
        .chain(task.kvars.iter().flat_map(|k| &k.sorts))
        .chain(
            task.define_funs
                .iter()
                .flat_map(|d| d.sort.inputs.iter().chain(std::iter::once(&d.sort.output))),
        )
    {
        collect_undeclared_sorts(sort, &declared_names, &mut declared, &mut undeclared);
    }
    for (name, arity) in undeclared {
        writeln!(f, "(declare-sort {name} {arity})")?;
    }

    // Datatypes must be declared after the datatypes they refer to (z3 rejects a mutual block
    // whose bodies use e.g. `Set` over a sibling), so emit them in dependency order. Any cycle
    // left over goes into one mutual block.
    for group in order_data_decls(&datatypes) {
        write!(f, "(declare-datatypes (")?;
        for decl in &group {
            write!(f, "({} {})", decl.name.display(), decl.vars)?;
        }
        write!(f, ") (")?;
        for decl in &group {
            fmt_data_decl_body_smt(decl, f)?;
        }
        writeln!(f, "))")?;
    }

    // Constant declarations. A constant pinned to a ground term by a guard is emitted as an
    // interpreted `define-fun`; see `find_const_definitions`.
    let const_defs = find_const_definitions(&task.constants, &clauses);
    let const_names: HashSet<&T::Var> = task.constants.iter().map(|c| &c.name).collect();
    let mut emitted: HashSet<&T::Var> = HashSet::new();
    for cinfo in &task.constants {
        // A definition may mention another constant, so only use it once everything it refers to
        // has been emitted; otherwise it would be a forward reference.
        let definable = const_defs.get(&cinfo.name).filter(|def| {
            // A function-sorted constant is declared with an arity, not defined as a value.
            if uncurry_func_sort(&cinfo.sort).is_some() {
                return false;
            }
            let mut vars = Vec::new();
            collect_vars(def, &mut vars);
            vars.iter()
                .all(|var| !const_names.contains(var) || emitted.contains(var))
        });
        match definable {
            Some(def) => {
                // This path bypasses `fmt_const_decl`, so carry the comment over too.
                if let Some(comment) = &cinfo.comment {
                    fmt_decl_comment(comment, f)?;
                }
                write!(f, "(define-fun {} () ", cinfo.name.display())?;
                fmt_sort_smt(&cinfo.sort, f)?;
                write!(f, " ")?;
                fmt_expr_smt(def, f)?;
                writeln!(f, ")")?;
            }
            None => fmt_const_decl(cinfo, f)?,
        }
        emitted.insert(&cinfo.name);
    }

    // Function definitions
    for fun_decl in &task.define_funs {
        fmt_fun_def(fun_decl, f)?;
    }

    // KVar declarations as uninterpreted Boolean functions
    for kvar in &task.kvars {
        fmt_kvar_as_fun(kvar, f)?;
    }

    writeln!(f)?;

    // Write assertions
    for clause in &clauses {
        fmt_assert(clause, f)?;
    }

    writeln!(f)?;
    writeln!(f, "(check-sat)")
}

fn fmt_kvar_as_fun<T: Types>(kvar: &KVarDecl<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt_decl_comment(&kvar.comment, f)?;
    write!(f, "(declare-fun {} (", kvar.kvid.display())?;
    for (i, sort) in kvar.sorts.iter().enumerate() {
        if i > 0 {
            write!(f, " ")?;
        }
        fmt_sort_smt(sort, f)?;
    }
    writeln!(f, ") Bool)")
}

fn fmt_assert<T: Types>(clause: &HornClause<'_, T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "(assert ")?;

    // Wrap in forall if there are variables
    if !clause.vars.is_empty() {
        write!(f, "(forall (")?;
        for (var, sort) in &clause.vars {
            write!(f, "({} ", var.display())?;
            fmt_sort_smt(sort, f)?;
            write!(f, ")")?;
        }
        write!(f, ") ")?;
    }

    match &clause.head {
        Pred::KVar(k, args) => {
            // (=> guards (k args))
            write!(f, "(=> ")?;
            fmt_guard_conjunction(&clause.guards, f)?;
            write!(f, " ({}", k.display())?;
            for arg in args {
                write!(f, " ")?;
                fmt_expr_smt(arg, f)?;
            }
            write!(f, "))")?;
        }
        Pred::Expr(e) => {
            // (=> (and guards (not e)) false)
            write!(f, "(=> ")?;
            let guard_count = clause.guards.len() + 1;
            if guard_count == 1 && clause.guards.is_empty() {
                write!(f, "(not ")?;
                fmt_expr_smt(e, f)?;
                write!(f, ")")?;
            } else {
                write!(f, "(and")?;
                for guard in &clause.guards {
                    write!(f, " ")?;
                    fmt_guard(guard, f)?;
                }
                write!(f, " (not ")?;
                fmt_expr_smt(e, f)?;
                write!(f, "))")?;
            }
            write!(f, " false)")?;
        }
    }

    // Close forall
    if !clause.vars.is_empty() {
        write!(f, ")")?;
    }

    writeln!(f, ")")
}

fn fmt_guard_conjunction<T: Types>(guards: &[&Pred<T>], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if guards.is_empty() {
        write!(f, "true")
    } else if guards.len() == 1 {
        fmt_guard(guards[0], f)
    } else {
        write!(f, "(and")?;
        for guard in guards {
            write!(f, " ")?;
            fmt_guard(guard, f)?;
        }
        write!(f, ")")
    }
}

fn fmt_guard<T: Types>(guard: &Pred<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match guard {
        Pred::KVar(k, args) => {
            write!(f, "({}", k.display())?;
            for arg in args {
                write!(f, " ")?;
                fmt_expr_smt(arg, f)?;
            }
            write!(f, ")")
        }
        Pred::Expr(e) => fmt_expr_smt(e, f),
    }
}

pub struct SmtFormatter<'a, T: Types>(pub &'a Task<T>);

impl<T: Types> fmt::Display for SmtFormatter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_smt_horn(self.0, f)
    }
}

// ---- SMT-LIB sort formatting ----

/// Names of the data sorts `sort` refers to.
fn data_sorts_of<T: Types>(sort: &Sort<T>, out: &mut Vec<String>) {
    match sort {
        Sort::Int | Sort::Bool | Sort::Real | Sort::Str | Sort::BvSize(_) | Sort::Var(_) => {}
        Sort::BitVec(sort) | Sort::Abs(_, sort) => data_sorts_of(sort, out),
        Sort::Func(sorts) => sorts.iter().for_each(|s| data_sorts_of(s, out)),
        Sort::App(ctor, sorts) => {
            if let SortCtor::Data(name) = ctor {
                out.push(name.display().to_string());
            }
            sorts.iter().for_each(|s| data_sorts_of(s, out));
        }
    }
}

/// Collects data sorts referenced by `sort` that have no declaration in the task, together with
/// the arity they are used at.
fn collect_undeclared_sorts<T: Types>(
    sort: &Sort<T>,
    declared_in_task: &HashSet<String>,
    seen: &mut HashSet<String>,
    out: &mut Vec<(String, usize)>,
) {
    match sort {
        Sort::Int | Sort::Bool | Sort::Real | Sort::Str | Sort::BvSize(_) | Sort::Var(_) => {}
        Sort::BitVec(sort) | Sort::Abs(_, sort) => {
            collect_undeclared_sorts(sort, declared_in_task, seen, out);
        }
        Sort::Func(sorts) => {
            for sort in sorts.iter() {
                collect_undeclared_sorts(sort, declared_in_task, seen, out);
            }
        }
        Sort::App(ctor, sorts) => {
            if let SortCtor::Data(name) = ctor {
                let name = name.display().to_string();
                if !declared_in_task.contains(&name) && seen.insert(name.clone()) {
                    out.push((name, sorts.len()));
                }
            }
            for sort in sorts {
                collect_undeclared_sorts(sort, declared_in_task, seen, out);
            }
        }
    }
}

/// Groups data declarations so that a group only refers to sorts declared by itself or an earlier
/// group. Mutually recursive declarations end up in the same group.
fn order_data_decls<'a, T: Types>(decls: &[&'a DataDecl<T>]) -> Vec<Vec<&'a DataDecl<T>>> {
    let index: HashMap<String, usize> = decls
        .iter()
        .enumerate()
        .map(|(i, decl)| (decl.name.display().to_string(), i))
        .collect();
    let deps: Vec<Vec<usize>> = decls
        .iter()
        .map(|decl| {
            let mut names = Vec::new();
            for field in decl.ctors.iter().flat_map(|ctor| &ctor.fields) {
                data_sorts_of(&field.sort, &mut names);
            }
            names
                .iter()
                .filter_map(|name| index.get(name).copied())
                .collect()
        })
        .collect();

    let mut groups = Vec::new();
    let mut emitted = vec![false; decls.len()];
    loop {
        let ready: Vec<usize> = (0..decls.len())
            .filter(|&i| !emitted[i] && deps[i].iter().all(|&j| j == i || emitted[j]))
            .collect();
        if ready.is_empty() {
            break;
        }
        for &i in &ready {
            emitted[i] = true;
        }
        groups.push(ready.iter().map(|&i| decls[i]).collect());
    }
    // Whatever is left is part of a cycle; emit it as a single mutual block.
    let rest: Vec<_> = (0..decls.len())
        .filter(|&i| !emitted[i])
        .map(|i| decls[i])
        .collect();
    if !rest.is_empty() {
        groups.push(rest);
    }
    groups
}

/// Records the largest sort variable index occurring in `sort`.
fn max_sort_var_of<T: Types>(sort: &Sort<T>, max: &mut Option<usize>) {
    match sort {
        Sort::Var(i) => *max = Some(max.map_or(*i, |m: usize| m.max(*i))),
        Sort::Int | Sort::Bool | Sort::Real | Sort::Str | Sort::BvSize(_) => {}
        Sort::BitVec(sort) | Sort::Abs(_, sort) => max_sort_var_of(sort, max),
        Sort::Func(sorts) => sorts.iter().for_each(|s| max_sort_var_of(s, max)),
        Sort::App(_, sorts) => sorts.iter().for_each(|s| max_sort_var_of(s, max)),
    }
}

/// Name used for a sort variable declared with `declare-type-var`.
const SORT_VAR_PREFIX: &str = "T";

/// Name used for a sort variable bound by the `par` binder of a parametric datatype. It must
/// differ from [`SORT_VAR_PREFIX`]: a `declare-type-var` of the same name takes precedence over
/// the `par` binder, and the datatype's parameter then never gets instantiated.
const DATA_SORT_VAR_PREFIX: &str = "Par";

fn fmt_sort_smt<T: Types>(sort: &Sort<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt_sort_smt_with(sort, SORT_VAR_PREFIX, f)
}

/// Formats `sort`, naming sort variables `{prefix}{i}`. Sort variables mean different things
/// depending on where the sort appears: inside a datatype declaration they refer to that
/// datatype's own parameters, everywhere else to a `declare-type-var`.
fn fmt_sort_smt_with<T: Types>(
    sort: &Sort<T>,
    prefix: &str,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    match sort {
        Sort::Int => write!(f, "Int"),
        Sort::Bool => write!(f, "Bool"),
        Sort::Real => write!(f, "Real"),
        Sort::Str => write!(f, "String"),
        Sort::BitVec(size) => {
            write!(f, "(_ BitVec ")?;
            fmt_sort_smt_with(size, prefix, f)?;
            write!(f, ")")
        }
        Sort::BvSize(size) => write!(f, "{size}"),
        Sort::Var(i) => write!(f, "{prefix}{i}"),
        // SMT-LIB has no function values: a function is a symbol with an arity, never something a
        // variable, field or predicate argument can hold. A function sort reaching here is used as
        // a value, and approximating it as `(Array input output)` would silently change what the
        // constraint means, so bail out and let the caller skip the task.
        //
        // A function sort in *declaration* position never reaches here; `fmt_const_decl` uncurries
        // it into a `declare-fun` with an arity instead.
        Sort::Func(_) => {
            panic!("Function sorts used as values are not supported in SMT/Horn format")
        }
        Sort::Abs(_, sort) => fmt_sort_smt_with(sort, prefix, f),
        Sort::App(ctor, args) => {
            if args.is_empty() {
                fmt_sort_ctor_smt(ctor, f)
            } else {
                write!(f, "(")?;
                fmt_sort_ctor_smt(ctor, f)?;
                for arg in args {
                    write!(f, " ")?;
                    fmt_sort_smt_with(arg, prefix, f)?;
                }
                write!(f, ")")
            }
        }
    }
}

fn fmt_sort_ctor_smt<T: Types>(ctor: &SortCtor<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match ctor {
        // z3 defines `(Set T)` as sugar for `(Array T Bool)`, so fixpoint's name works as is. There
        // is no such alias for `Map`: SMT-LIB calls the theory `Array`, which is what the map
        // operations already compile to (`MapSelect` -> `select`, `MapStore` -> `store`).
        SortCtor::Set => write!(f, "Set"),
        SortCtor::Map => write!(f, "Array"),
        SortCtor::Data(name) => write!(f, "{}", name.display()),
    }
}

// ---- SMT-LIB expression formatting ----

fn fmt_expr_smt<T: Types>(expr: &Expr<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match expr {
        Expr::Constant(c) => fmt_constant_smt(c, f),
        Expr::Var(x) => write!(f, "{}", x.display()),
        Expr::App(func, sort_args, args, _out_sort) => {
            // Some theory operators can't be printed as a plain symbol applied to its arguments:
            // they need the sort they are used at, or a different argument order.
            if let Expr::ThyFunc(thy_func) = &**func
                && let Some(app) = fmt_thy_func_app_smt(*thy_func, sort_args.as_deref(), args, f)
            {
                return app;
            }
            // A nullary application must be printed as a bare symbol: `(f)` is not valid SMT-LIB.
            if args.is_empty() {
                return fmt_expr_smt(func, f);
            }
            write!(f, "(")?;
            fmt_expr_smt(func, f)?;
            for arg in args {
                write!(f, " ")?;
                fmt_expr_smt(arg, f)?;
            }
            write!(f, ")")
        }
        Expr::Neg(e) => {
            write!(f, "(- ")?;
            fmt_expr_smt(e, f)?;
            write!(f, ")")
        }
        Expr::BinaryOp(op, exprs) => {
            let [e1, e2] = &**exprs;
            write!(f, "({} ", fmt_binop_smt(*op))?;
            fmt_expr_smt(e1, f)?;
            write!(f, " ")?;
            fmt_expr_smt(e2, f)?;
            write!(f, ")")
        }
        Expr::IfThenElse(exprs) => {
            let [p, e1, e2] = &**exprs;
            write!(f, "(ite ")?;
            fmt_expr_smt(p, f)?;
            write!(f, " ")?;
            fmt_expr_smt(e1, f)?;
            write!(f, " ")?;
            fmt_expr_smt(e2, f)?;
            write!(f, ")")
        }
        Expr::And(exprs) => {
            if exprs.is_empty() {
                write!(f, "true")
            } else {
                write!(f, "(and")?;
                for e in exprs {
                    write!(f, " ")?;
                    fmt_expr_smt(e, f)?;
                }
                write!(f, ")")
            }
        }
        Expr::Or(exprs) => {
            if exprs.is_empty() {
                write!(f, "false")
            } else {
                write!(f, "(or")?;
                for e in exprs {
                    write!(f, " ")?;
                    fmt_expr_smt(e, f)?;
                }
                write!(f, ")")
            }
        }
        Expr::Not(e) => {
            write!(f, "(not ")?;
            fmt_expr_smt(e, f)?;
            write!(f, ")")
        }
        Expr::Imp(exprs) => {
            let [e1, e2] = &**exprs;
            write!(f, "(=> ")?;
            fmt_expr_smt(e1, f)?;
            write!(f, " ")?;
            fmt_expr_smt(e2, f)?;
            write!(f, ")")
        }
        Expr::Iff(exprs) => {
            let [e1, e2] = &**exprs;
            write!(f, "(= ")?;
            fmt_expr_smt(e1, f)?;
            write!(f, " ")?;
            fmt_expr_smt(e2, f)?;
            write!(f, ")")
        }
        Expr::Atom(rel, exprs) => {
            let [e1, e2] = &**exprs;
            fmt_binrel_smt(*rel, e1, e2, f)
        }
        Expr::Let(name, exprs) => {
            let [e1, e2] = &**exprs;
            write!(f, "(let (({} ", name.display())?;
            fmt_expr_smt(e1, f)?;
            write!(f, ")) ")?;
            fmt_expr_smt(e2, f)?;
            write!(f, ")")
        }
        Expr::ThyFunc(thy_func) => fmt_thy_func_smt(thy_func, f),
        Expr::IsCtor(ctor, e) => {
            write!(f, "((_ is {}) ", ctor.display())?;
            fmt_expr_smt(e, f)?;
            write!(f, ")")
        }
        Expr::Quantifier(..) => {
            panic!("Quantifiers are not supported in SMT/Horn format");
        }
        // Weak kvars are internal placeholders and are not part of the Horn encoding.
        Expr::WKVar(..) => {
            // These could either be encoded as true (to ignore solving them)
            // or in the same way kvars are (to solve for them)
            panic!("Weak KVars not supported in SMT/Horn format")
        }
    }
}

fn fmt_constant_smt<T: Types>(c: &Constant<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match c {
        Constant::Numeral(n) => write!(f, "{n}"),
        Constant::Real(n) => write!(f, "{}", n.display()),
        Constant::Boolean(b) => write!(f, "{b}"),
        Constant::String(s) => write!(f, "\"{}\"", s.display()),
        Constant::BitVec(val, size) => write!(f, "(_ bv{val} {size})"),
    }
}

fn fmt_binop_smt(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "div",
        BinOp::Mod => "mod",
    }
}

fn fmt_binrel_smt<T: Types>(
    rel: BinRel,
    e1: &Expr<T>,
    e2: &Expr<T>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    match rel {
        BinRel::Ne => {
            write!(f, "(not (= ")?;
            fmt_expr_smt(e1, f)?;
            write!(f, " ")?;
            fmt_expr_smt(e2, f)?;
            write!(f, "))")
        }
        _ => {
            let op = match rel {
                BinRel::Eq => "=",
                BinRel::Gt => ">",
                BinRel::Ge => ">=",
                BinRel::Lt => "<",
                BinRel::Le => "<=",
                BinRel::Ne => unreachable!(),
            };
            write!(f, "({op} ")?;
            fmt_expr_smt(e1, f)?;
            write!(f, " ")?;
            fmt_expr_smt(e2, f)?;
            write!(f, ")")
        }
    }
}

/// Formats the theory operators that can't be printed as a symbol applied to its arguments,
/// returning `None` for the ones that can (which the caller then prints the plain way).
///
/// Sets are arrays to `Bool` in z3, and the operators that build one out of nothing need the
/// element sort spelled out at the use site, which a bare symbol can't carry. `union`,
/// `intersection`, `setminus` and `subset` are real z3 symbols and are left alone.
fn fmt_thy_func_app_smt<T: Types>(
    thy_func: ThyFunc,
    sort_args: Option<&[Sort<T>]>,
    args: &[Expr<T>],
    f: &mut fmt::Formatter<'_>,
) -> Option<fmt::Result> {
    /// `((as const (Set E)) false)`, i.e. the set that contains nothing.
    fn empty_set<T: Types>(elem: &Sort<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "((as const (Set ")?;
        fmt_sort_smt(elem, f)?;
        write!(f, ")) false)")
    }

    // The element sort is only carried by applications encoded from `rty::ExprKind::App`. Without
    // it there is nothing to fill the `as` annotation with, so bail out and skip the task rather
    // than guess a sort that then fails to typecheck somewhere else.
    let elem_sort = || {
        let Some([sort, ..]) = sort_args else {
            panic!("Set operations without a sort argument are not supported in SMT/Horn format")
        };
        sort
    };

    match thy_func {
        // Fixpoint's `Set_empty` takes a dummy argument, which has no counterpart here.
        ThyFunc::SetEmpty => Some(empty_set(elem_sort(), f)),
        // z3 has no `singleton`: build it by storing the element into the empty set.
        ThyFunc::SetSng if args.len() == 1 => {
            Some((|| {
                write!(f, "(store ")?;
                empty_set(elem_sort(), f)?;
                write!(f, " ")?;
                fmt_expr_smt(&args[0], f)?;
                write!(f, " true)")
            })())
        }
        // z3 has no `member` either, and a set is just an array, so membership is a lookup. Note
        // the argument order flips: fixpoint's `member(x, s)` is `(select s x)`.
        ThyFunc::SetMem if args.len() == 2 => {
            Some((|| {
                write!(f, "(select ")?;
                fmt_expr_smt(&args[1], f)?;
                write!(f, " ")?;
                fmt_expr_smt(&args[0], f)?;
                write!(f, ")")
            })())
        }
        // `(const v)` is the constant map, which needs its sort the same way the empty set does.
        ThyFunc::MapDefault if args.len() == 1 => {
            Some((|| {
                let Some([key, value, ..]) = sort_args else {
                    panic!("Map default without sort arguments is not supported in SMT/Horn format")
                };
                write!(f, "((as const (Array ")?;
                fmt_sort_smt(key, f)?;
                write!(f, " ")?;
                fmt_sort_smt(value, f)?;
                write!(f, ")) ")?;
                fmt_expr_smt(&args[0], f)?;
                write!(f, ")")
            })())
        }
        _ => None,
    }
}

fn fmt_thy_func_smt(thy_func: &ThyFunc, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match thy_func {
        ThyFunc::StrLen => write!(f, "str.len"),
        ThyFunc::StrConcat => write!(f, "str.++"),
        ThyFunc::StrPrefixOf => write!(f, "str.prefixof"),
        ThyFunc::StrSuffixOf => write!(f, "str.suffixof"),
        ThyFunc::StrContains => write!(f, "str.contains"),
        ThyFunc::BvZeroExtend(size) => write!(f, "(_ zero_extend {size})"),
        ThyFunc::BvSignExtend(size) => write!(f, "(_ sign_extend {size})"),
        ThyFunc::IntToBv8 => write!(f, "(_ int2bv 8)"),
        ThyFunc::Bv8ToInt => write!(f, "bv2int"),
        ThyFunc::IntToBv32 => write!(f, "(_ int2bv 32)"),
        ThyFunc::Bv32ToInt => write!(f, "bv2int"),
        ThyFunc::IntToBv64 => write!(f, "(_ int2bv 64)"),
        ThyFunc::Bv64ToInt => write!(f, "bv2int"),
        ThyFunc::BvUle => write!(f, "bvule"),
        ThyFunc::BvSle => write!(f, "bvsle"),
        ThyFunc::BvUge => write!(f, "bvuge"),
        ThyFunc::BvSge => write!(f, "bvsge"),
        ThyFunc::BvUdiv => write!(f, "bvudiv"),
        ThyFunc::BvSdiv => write!(f, "bvsdiv"),
        ThyFunc::BvSrem => write!(f, "bvsrem"),
        ThyFunc::BvUrem => write!(f, "bvurem"),
        ThyFunc::BvLshr => write!(f, "bvlshr"),
        ThyFunc::BvAshr => write!(f, "bvashr"),
        ThyFunc::BvAnd => write!(f, "bvand"),
        ThyFunc::BvOr => write!(f, "bvor"),
        ThyFunc::BvXor => write!(f, "bvxor"),
        ThyFunc::BvNot => write!(f, "bvnot"),
        ThyFunc::BvAdd => write!(f, "bvadd"),
        ThyFunc::BvNeg => write!(f, "bvneg"),
        ThyFunc::BvSub => write!(f, "bvsub"),
        ThyFunc::BvMul => write!(f, "bvmul"),
        ThyFunc::BvShl => write!(f, "bvshl"),
        ThyFunc::BvUgt => write!(f, "bvugt"),
        ThyFunc::BvSgt => write!(f, "bvsgt"),
        ThyFunc::BvUlt => write!(f, "bvult"),
        ThyFunc::BvSlt => write!(f, "bvslt"),
        // These have no symbol of their own in z3; `fmt_thy_func_app_smt` rewrites them where they
        // are applied. Reaching here means one appeared outside an application, where there is no
        // sort to build it from.
        ThyFunc::SetEmpty | ThyFunc::SetSng | ThyFunc::SetMem | ThyFunc::MapDefault => {
            panic!("`{thy_func:?}` outside an application is not supported in SMT/Horn format")
        }
        ThyFunc::SetCup => write!(f, "union"),
        ThyFunc::SetCap => write!(f, "intersection"),
        ThyFunc::SetDif => write!(f, "setminus"),
        ThyFunc::SetSub => write!(f, "subset"),
        ThyFunc::MapSelect => write!(f, "select"),
        ThyFunc::MapStore => write!(f, "store"),
    }
}

// ---- Data type / constant / function declaration formatting ----

/// Formats the constructor list of a datatype, i.e. the part that goes in the second argument of
/// `declare-datatypes`.
fn fmt_data_decl_body_smt<T: Types>(decl: &DataDecl<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    // A parametric datatype must bind its type variables with `par`.
    if decl.vars > 0 {
        write!(f, "(par (")?;
        for i in 0..decl.vars {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{DATA_SORT_VAR_PREFIX}{i}")?;
        }
        write!(f, ") (")?;
    } else {
        write!(f, "(")?;
    }
    for (i, ctor) in decl.ctors.iter().enumerate() {
        if i > 0 {
            write!(f, " ")?;
        }
        fmt_data_ctor_smt(ctor, f)?;
    }
    // Two opens to close on the parametric path: `(par` and the constructor list. The `par`
    // binder list is balanced above.
    if decl.vars > 0 { write!(f, "))") } else { write!(f, ")") }
}

fn fmt_data_ctor_smt<T: Types>(ctor: &DataCtor<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({}", ctor.name.display())?;
    for field in &ctor.fields {
        write!(f, " ({} ", field.name.display())?;
        // A sort variable in a field refers to the enclosing datatype's `par` binder.
        fmt_sort_smt_with(&field.sort, DATA_SORT_VAR_PREFIX, f)?;
        write!(f, ")")?;
    }
    write!(f, ")")
}

/// Splits a (possibly polymorphic, curried) function sort into its argument sorts and its result,
/// e.g. `∀a. a -> a -> bool` becomes `([a, a], bool)`. Returns `None` for a non-function sort.
fn uncurry_func_sort<T: Types>(sort: &Sort<T>) -> Option<(Vec<&Sort<T>>, &Sort<T>)> {
    let mut sort = sort;
    // Sort variables bound here are declared globally with `declare-type-var`.
    while let Sort::Abs(_, inner) = sort {
        sort = inner;
    }
    let mut inputs = Vec::new();
    while let Sort::Func(fsort) = sort {
        let [input, output] = &**fsort;
        inputs.push(input);
        sort = output;
    }
    (!inputs.is_empty()).then_some((inputs, sort))
}

/// Writes a declaration's comment as an SMT-LIB line comment.
///
/// These say what a generated name actually is -- `prim op uif: Shl`, `alias reft: ...`,
/// `rust const: ...` -- which is otherwise unrecoverable from the `c0`/`k3` names alone. The text
/// comes from `{:?}` of flux internals, so it can span lines; a comment ends at the newline, so
/// the whole thing is flattened onto one.
fn fmt_decl_comment(comment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let comment = comment.trim();
    if comment.is_empty() {
        return Ok(());
    }
    writeln!(f, ";; {}", comment.split_whitespace().collect::<Vec<_>>().join(" "))
}

fn fmt_const_decl<T: Types>(decl: &ConstDecl<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(comment) = &decl.comment {
        fmt_decl_comment(comment, f)?;
    }
    // A constant of function sort is an uninterpreted function, so declare it with an arity rather
    // than as a value of some approximated sort. Spacer accepts the declaration and only rejects a
    // rule that actually applies it, which is the honest outcome: an unused declaration (the
    // polymorphic `gt`/`ge`/`lt`/`le` relations every task carries) costs nothing, and a used one
    // is reported as unsupported instead of being silently reinterpreted.
    if let Some((inputs, output)) = uncurry_func_sort(&decl.sort) {
        write!(f, "(declare-fun {} (", decl.name.display())?;
        for (i, input) in inputs.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            fmt_sort_smt(input, f)?;
        }
        write!(f, ") ")?;
        fmt_sort_smt(output, f)?;
        return writeln!(f, ")");
    }
    write!(f, "(declare-const {} ", decl.name.display())?;
    fmt_sort_smt(&decl.sort, f)?;
    writeln!(f, ")")
}

fn fmt_fun_def<T: Types>(fun: &FunDef<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(comment) = &fun.comment {
        fmt_decl_comment(comment, f)?;
    }
    if let Some(body) = &fun.body {
        write!(f, "(define-fun {} (", fun.name.display())?;
        for (i, (name, sort)) in body.args.iter().zip(&fun.sort.inputs).enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "({} ", name.display())?;
            fmt_sort_smt(sort, f)?;
            write!(f, ")")?;
        }
        write!(f, ") ")?;
        fmt_sort_smt(&fun.sort.output, f)?;
        write!(f, " ")?;
        fmt_expr_smt(&body.expr, f)?;
        writeln!(f, ")")
    } else {
        write!(f, "(declare-fun {} (", fun.name.display())?;
        for (i, sort) in fun.sort.inputs.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            fmt_sort_smt(sort, f)?;
        }
        write!(f, ") ")?;
        fmt_sort_smt(&fun.sort.output, f)?;
        writeln!(f, ")")
    }
}
