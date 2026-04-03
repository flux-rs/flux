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
use std::fmt;

use crate::{
    Constraint, Expr, Identifier, KVarDecl, Pred, Sort, Task,
    Types,
};

use crate::format_datalog::{
    fmt_const_decl_datalog, fmt_data_decl_smt, fmt_expr_smt,
    fmt_fun_def_datalog, fmt_sort_smt,
};

/// A flattened Horn clause extracted from the constraint tree.
struct HornClause<'a, T: Types> {
    /// Universally quantified variables with their sorts
    vars: Vec<(&'a T::Var, &'a Sort<T>)>,
    /// Guard predicates (body of the implication)
    guards: Vec<Guard<'a, T>>,
    /// Head of the clause
    head: Head<'a, T>,
}

/// A guard (body element) in a Horn clause
enum Guard<'a, T: Types> {
    KVar(&'a T::KVar, &'a [Expr<T>]),
    Expr(&'a Expr<T>),
}

/// Head (conclusion) of a Horn clause
enum Head<'a, T: Types> {
    /// Head is a KVar application
    KVar(&'a T::KVar, &'a [Expr<T>]),
    /// Head is a concrete expression that must hold (negated → false for query)
    Query(&'a Expr<T>),
}

/// Collect all Horn clauses from a constraint tree
fn flatten_constraint<'a, T: Types>(
    constraint: &'a Constraint<T>,
    vars: &mut Vec<(&'a T::Var, &'a Sort<T>)>,
    guards: &mut Vec<Guard<'a, T>>,
    clauses: &mut Vec<HornClause<'a, T>>,
) {
    match constraint {
        Constraint::ForAll(bind, body) => {
            vars.push((&bind.name, &bind.sort));
            push_pred_as_guards(&bind.pred, guards);
            flatten_constraint(body, vars, guards, clauses);
            pop_pred_guards(&bind.pred, guards);
            vars.pop();
        }
        Constraint::Conj(cstrs) => {
            for cstr in cstrs {
                flatten_constraint(cstr, vars, guards, clauses);
            }
        }
        Constraint::Pred(pred, _tag) => {
            flatten_pred_head(pred, vars, guards, clauses);
        }
    }
}

fn push_pred_as_guards<'a, T: Types>(pred: &'a Pred<T>, guards: &mut Vec<Guard<'a, T>>) {
    match pred {
        Pred::And(preds) => {
            for p in preds {
                push_pred_as_guards(p, guards);
            }
        }
        Pred::KVar(k, args) => guards.push(Guard::KVar(k, args)),
        Pred::Expr(e) => {
            if !is_trivially_true_expr(e) {
                guards.push(Guard::Expr(e));
            }
        }
    }
}

fn pop_pred_guards<T: Types>(pred: &Pred<T>, guards: &mut Vec<Guard<'_, T>>) {
    match pred {
        Pred::And(preds) => {
            for p in preds {
                pop_pred_guards(p, guards);
            }
        }
        Pred::KVar(..) => {
            guards.pop();
        }
        Pred::Expr(e) => {
            if !is_trivially_true_expr(e) {
                guards.pop();
            }
        }
    }
}

fn flatten_pred_head<'a, T: Types>(
    pred: &'a Pred<T>,
    vars: &[(&'a T::Var, &'a Sort<T>)],
    guards: &[Guard<'a, T>],
    clauses: &mut Vec<HornClause<'a, T>>,
) {
    match pred {
        Pred::And(preds) => {
            for p in preds {
                flatten_pred_head(p, vars, guards, clauses);
            }
        }
        Pred::KVar(k, args) => {
            clauses.push(HornClause {
                vars: vars.to_vec(),
                guards: clone_guards(guards),
                head: Head::KVar(k, args),
            });
        }
        Pred::Expr(e) => {
            if is_trivially_true_expr(e) {
                return;
            }
            clauses.push(HornClause {
                vars: vars.to_vec(),
                guards: clone_guards(guards),
                head: Head::Query(e),
            });
        }
    }
}

fn clone_guards<'a, T: Types>(guards: &[Guard<'a, T>]) -> Vec<Guard<'a, T>> {
    guards
        .iter()
        .map(|g| match *g {
            Guard::KVar(k, args) => Guard::KVar(k, args),
            Guard::Expr(e) => Guard::Expr(e),
        })
        .collect()
}

fn is_trivially_true_expr<T: Types>(e: &Expr<T>) -> bool {
    matches!(e, Expr::Constant(crate::Constant::Boolean(true)))
}

/// Format a task in the SMT-LIB HORN CHC format
pub(crate) fn fmt_smt_task<T: Types>(
    task: &Task<T>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
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

    // Data type declarations
    for data_decl in &task.data_decls {
        fmt_data_decl_smt(data_decl, f)?;
    }

    // Constant declarations
    for cinfo in &task.constants {
        fmt_const_decl_datalog(cinfo, f)?;
    }

    // Function definitions
    for fun_decl in &task.define_funs {
        fmt_fun_def_datalog(fun_decl, f)?;
    }

    // KVar declarations as uninterpreted Boolean functions
    for kvar in &task.kvars {
        fmt_kvar_as_fun(kvar, f)?;
    }

    writeln!(f)?;

    // Flatten constraints into Horn clauses
    let mut clauses = Vec::new();
    let mut vars = Vec::new();
    let mut guards = Vec::new();
    flatten_constraint(
        &task.constraint,
        &mut vars,
        &mut guards,
        &mut clauses,
    );

    // Write assertions
    for clause in &clauses {
        fmt_assert(clause, f)?;
    }

    writeln!(f)?;
    writeln!(f, "(check-sat)")
}

fn fmt_kvar_as_fun<T: Types>(kvar: &KVarDecl<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
        Head::KVar(k, args) => {
            // (=> guards (k args))
            write!(f, "(=> ")?;
            fmt_guard_conjunction(&clause.guards, f)?;
            write!(f, " ({}", k.display())?;
            for arg in *args {
                write!(f, " ")?;
                fmt_expr_smt(arg, f)?;
            }
            write!(f, "))")?;
        }
        Head::Query(e) => {
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

fn fmt_guard_conjunction<T: Types>(
    guards: &[Guard<'_, T>],
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    if guards.is_empty() {
        write!(f, "true")
    } else if guards.len() == 1 {
        fmt_guard(&guards[0], f)
    } else {
        write!(f, "(and")?;
        for guard in guards {
            write!(f, " ")?;
            fmt_guard(guard, f)?;
        }
        write!(f, ")")
    }
}

fn fmt_guard<T: Types>(guard: &Guard<'_, T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match guard {
        Guard::KVar(k, args) => {
            write!(f, "({}", k.display())?;
            for arg in *args {
                write!(f, " ")?;
                fmt_expr_smt(arg, f)?;
            }
            write!(f, ")")
        }
        Guard::Expr(e) => fmt_expr_smt(e, f),
    }
}

/// Write a task to a string in SMT-LIB HORN CHC format
pub(crate) fn task_to_smt_string<T: Types>(task: &Task<T>) -> String {
    struct SmtFormatter<'a, T: Types>(&'a Task<T>);

    impl<T: Types> fmt::Display for SmtFormatter<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt_smt_task(self.0, f)
        }
    }

    format!("{}", SmtFormatter(task))
}
