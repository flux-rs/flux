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
use std::fmt::{self, Write};

use crate::{
    Constraint, Identifier, KVarDecl, Pred, Sort, Task, Types,
    smt_fmt::{SmtEncodeError, SmtEncoder, SmtOptions},
};

/// A flattened Horn clause extracted from the constraint tree.
struct HornClause<'a, T: Types> {
    vars: Vec<(&'a T::Var, &'a Sort<T>)>,
    guards: Vec<&'a Pred<T>>,
    head: &'a Pred<T>,
}

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
            if !head.is_trivially_true() {
                clauses.push(HornClause { vars: vars.clone(), guards: guards.clone(), head });
            }
        }
    }
}

/// Format a task in the SMT-LIB HORN CHC format.
pub fn fmt_smt_horn<T: Types>(task: &Task<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    // Display cannot expose semantic encoding errors. Preserve the public formatting API,
    // while keeping structured errors throughout the shared encoder and internal helpers.
    write_smt_horn(task, f).map_err(|_| fmt::Error)
}

fn write_smt_horn<T: Types>(task: &Task<T>, out: &mut impl Write) -> Result<(), SmtEncodeError> {
    let encoder = SmtEncoder::new(&task.data_decls, SmtOptions::HORN);
    writeln!(out, "(set-logic HORN)\n")?;
    for line in &task.comments {
        writeln!(out, ";; {line}")?;
    }
    if !task.comments.is_empty() {
        writeln!(out)?;
    }
    for decl in &task.data_decls {
        encoder.write_datatype_decl(out, decl)?;
    }
    for decl in &task.constants {
        encoder.write_const_decl(out, &decl.name.display().to_string(), &decl.sort)?;
    }
    for fun in &task.define_funs {
        encoder.write_fun_def(out, fun)?;
    }
    for kvar in &task.kvars {
        write_kvar_decl(&encoder, kvar, out)?;
    }
    writeln!(out)?;

    let mut clauses = Vec::new();
    flatten_constraint(&task.constraint, &mut Vec::new(), &mut Vec::new(), &mut clauses);
    for clause in &clauses {
        write_assert(&encoder, clause, out)?;
    }
    writeln!(out, "\n(check-sat)")?;
    Ok(())
}

fn write_kvar_decl<T: Types>(
    encoder: &SmtEncoder<T>,
    kvar: &KVarDecl<T>,
    out: &mut impl Write,
) -> Result<(), SmtEncodeError> {
    write!(out, "(declare-fun {} (", kvar.kvid.display())?;
    for (i, sort) in kvar.sorts.iter().enumerate() {
        if i != 0 {
            out.write_char(' ')?;
        }
        encoder.write_sort(out, sort)?;
    }
    writeln!(out, ") Bool)")?;
    Ok(())
}

fn write_assert<T: Types>(
    encoder: &SmtEncoder<T>,
    clause: &HornClause<'_, T>,
    out: &mut impl Write,
) -> Result<(), SmtEncodeError> {
    write!(out, "(assert ")?;
    if !clause.vars.is_empty() {
        write!(out, "(forall (")?;
        for (var, sort) in &clause.vars {
            write!(out, "({} ", var.display())?;
            encoder.write_sort(out, sort)?;
            write!(out, ")")?;
        }
        write!(out, ") ")?;
    }
    write!(out, "(=> ")?;
    match clause.head {
        Pred::KVar(..) => {
            write_guard_conjunction(encoder, &clause.guards, out)?;
            out.write_char(' ')?;
            encoder.write_pred(out, clause.head)?;
            out.write_char(')')?;
        }
        Pred::Expr(expr) => {
            if !clause.guards.is_empty() {
                write!(out, "(and")?;
                for guard in &clause.guards {
                    out.write_char(' ')?;
                    encoder.write_pred(out, guard)?;
                }
                out.write_char(' ')?;
            }
            write!(out, "(not ")?;
            encoder.write_expr(out, expr)?;
            out.write_char(')')?;
            if !clause.guards.is_empty() {
                out.write_char(')')?;
            }
            write!(out, " false)")?;
        }
    }
    if !clause.vars.is_empty() {
        out.write_char(')')?;
    }
    writeln!(out, ")")?;
    Ok(())
}

fn write_guard_conjunction<T: Types>(
    encoder: &SmtEncoder<T>,
    guards: &[&Pred<T>],
    out: &mut impl Write,
) -> Result<(), SmtEncodeError> {
    match guards {
        [] => out.write_str("true")?,
        [guard] => encoder.write_pred(out, guard)?,
        _ => {
            write!(out, "(and")?;
            for guard in guards {
                out.write_char(' ')?;
                encoder.write_pred(out, guard)?;
            }
            out.write_char(')')?;
        }
    }
    Ok(())
}

pub struct SmtFormatter<'a, T: Types>(pub &'a Task<T>);

impl<T: Types> fmt::Display for SmtFormatter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_smt_horn(self.0, f)
    }
}
