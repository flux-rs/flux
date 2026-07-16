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
            guards.extend(bind.preds.iter().filter(|a| a.is_trivially_true()));
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

    // Data type declarations
    for data_decl in &task.data_decls {
        fmt_data_decl_smt(data_decl, f)?;
    }

    // Constant declarations
    for cinfo in &task.constants {
        fmt_const_decl(cinfo, f)?;
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

    // Flatten constraints into Horn clauses
    let mut clauses = Vec::new();
    let mut vars = Vec::new();
    let mut guards = Vec::new();
    flatten_constraint(&task.constraint, &mut vars, &mut guards, &mut clauses);

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

fn fmt_sort_smt<T: Types>(sort: &Sort<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match sort {
        Sort::Int => write!(f, "Int"),
        Sort::Bool => write!(f, "Bool"),
        Sort::Real => write!(f, "Real"),
        Sort::Str => write!(f, "String"),
        Sort::BitVec(size) => {
            write!(f, "(_ BitVec ")?;
            fmt_sort_smt(size, f)?;
            write!(f, ")")
        }
        Sort::BvSize(size) => write!(f, "{size}"),
        Sort::Var(i) => write!(f, "T{i}"),
        Sort::Func(fsort) => {
            // Function sorts mapped to (Array input output) as an approximation
            let [input, output] = &**fsort;
            write!(f, "(Array ")?;
            fmt_sort_smt(input, f)?;
            write!(f, " ")?;
            fmt_sort_smt(output, f)?;
            write!(f, ")")
        }
        Sort::Abs(_, sort) => fmt_sort_smt(sort, f),
        Sort::App(ctor, args) => {
            if args.is_empty() {
                fmt_sort_ctor_smt(ctor, f)
            } else {
                write!(f, "(")?;
                fmt_sort_ctor_smt(ctor, f)?;
                for arg in args {
                    write!(f, " ")?;
                    fmt_sort_smt(arg, f)?;
                }
                write!(f, ")")
            }
        }
    }
}

fn fmt_sort_ctor_smt<T: Types>(ctor: &SortCtor<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match ctor {
        SortCtor::Set => write!(f, "Set"),
        SortCtor::Map => write!(f, "Map"),
        SortCtor::Data(name) => write!(f, "{}", name.display()),
    }
}

// ---- SMT-LIB expression formatting ----

fn fmt_expr_smt<T: Types>(expr: &Expr<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match expr {
        Expr::Constant(c) => fmt_constant_smt(c, f),
        Expr::Var(x) => write!(f, "{}", x.display()),
        Expr::App(func, _sort_args, args, _out_sort) => {
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
        ThyFunc::SetEmpty => write!(f, "as emptyset"),
        ThyFunc::SetSng => write!(f, "singleton"),
        ThyFunc::SetCup => write!(f, "union"),
        ThyFunc::SetCap => write!(f, "intersection"),
        ThyFunc::SetDif => write!(f, "setminus"),
        ThyFunc::SetMem => write!(f, "member"),
        ThyFunc::SetSub => write!(f, "subset"),
        ThyFunc::MapDefault => write!(f, "const"),
        ThyFunc::MapSelect => write!(f, "select"),
        ThyFunc::MapStore => write!(f, "store"),
    }
}

// ---- Data type / constant / function declaration formatting ----

fn fmt_data_decl_smt<T: Types>(decl: &DataDecl<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if decl.ctors.is_empty() {
        write!(f, "(declare-sort {} {})", decl.name.display(), decl.vars)?;
        writeln!(f)
    } else {
        write!(f, "(declare-datatypes (")?;
        write!(f, "({} {})", decl.name.display(), decl.vars)?;
        write!(f, ") ((")?;
        for (i, ctor) in decl.ctors.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            fmt_data_ctor_smt(ctor, f)?;
        }
        writeln!(f, ")))")
    }
}

fn fmt_data_ctor_smt<T: Types>(ctor: &DataCtor<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({}", ctor.name.display())?;
    for field in &ctor.fields {
        write!(f, " ({} ", field.name.display())?;
        fmt_sort_smt(&field.sort, f)?;
        write!(f, ")")?;
    }
    write!(f, ")")
}

fn fmt_const_decl<T: Types>(decl: &ConstDecl<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "(declare-const {} ", decl.name.display())?;
    fmt_sort_smt(&decl.sort, f)?;
    writeln!(f, ")")
}

fn fmt_fun_def<T: Types>(fun: &FunDef<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
