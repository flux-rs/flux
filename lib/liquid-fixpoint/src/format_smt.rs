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
    Identifier, KVarDecl, Pred, Sort, SortCtor, Task, ThyFunc, Types,
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
    tagged_heads: &mut Vec<&'a T::Tag>,
) {
    match constraint {
        Constraint::ForAll(bind, body) => {
            vars.push((&bind.name, &bind.sort));
            push_pred_as_guards(&bind.pred, guards);
            flatten_constraint(body, vars, guards, clauses, tagged_heads);
            pop_pred_guards(&bind.pred, guards);
            vars.pop();
        }
        Constraint::Conj(cstrs) => {
            for cstr in cstrs {
                flatten_constraint(cstr, vars, guards, clauses, tagged_heads);
            }
        }
        Constraint::Pred(pred, tag) => {
            flatten_pred_head(pred, tag.as_ref(), vars, guards, clauses, tagged_heads);
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
    tag: Option<&'a T::Tag>,
    vars: &[(&'a T::Var, &'a Sort<T>)],
    guards: &[Guard<'a, T>],
    clauses: &mut Vec<HornClause<'a, T>>,
    tagged_heads: &mut Vec<&'a T::Tag>,
) {
    match pred {
        Pred::And(preds) => {
            for p in preds {
                flatten_pred_head(p, tag, vars, guards, clauses, tagged_heads);
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
            if let Some(tag) = tag {
                tagged_heads.push(tag);
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
    matches!(e, Expr::Constant(Constant::Boolean(true)))
}

/// Collect all tagged concrete heads from the constraint tree (used for unsafe result reporting)
pub(crate) fn collect_tagged_heads<T: Types>(constraint: &Constraint<T>) -> Vec<T::Tag> {
    let mut clauses = Vec::new();
    let mut tagged_heads = Vec::new();
    let mut vars = Vec::new();
    let mut guards = Vec::new();
    flatten_constraint(
        constraint,
        &mut vars,
        &mut guards,
        &mut clauses,
        &mut tagged_heads,
    );
    tagged_heads.into_iter().cloned().collect()
}

// ---- SMT-LIB HORN CHC task formatting ----

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
    let mut tagged_heads = Vec::new();
    let mut vars = Vec::new();
    let mut guards = Vec::new();
    flatten_constraint(
        &task.constraint,
        &mut vars,
        &mut guards,
        &mut clauses,
        &mut tagged_heads,
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
        Expr::Exists(binds, body) => {
            write!(f, "(exists (")?;
            for (name, sort) in binds {
                write!(f, "({} ", name.display())?;
                fmt_sort_smt(sort, f)?;
                write!(f, ")")?;
            }
            write!(f, ") ")?;
            fmt_expr_smt(body, f)?;
            write!(f, ")")
        }
    }
}

fn fmt_constant_smt<T: Types>(c: &Constant<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match c {
        Constant::Numeral(n) => write!(f, "{n}"),
        Constant::Real(n) => write!(f, "{n}.0"),
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
        _ => {
            // For bitvector, set, and map operations, use SMT-LIB standard names
            let name = match thy_func {
                ThyFunc::BvUle => "bvule",
                ThyFunc::BvSle => "bvsle",
                ThyFunc::BvUge => "bvuge",
                ThyFunc::BvSge => "bvsge",
                ThyFunc::BvUdiv => "bvudiv",
                ThyFunc::BvSdiv => "bvsdiv",
                ThyFunc::BvSrem => "bvsrem",
                ThyFunc::BvUrem => "bvurem",
                ThyFunc::BvLshr => "bvlshr",
                ThyFunc::BvAshr => "bvashr",
                ThyFunc::BvAnd => "bvand",
                ThyFunc::BvOr => "bvor",
                ThyFunc::BvXor => "bvxor",
                ThyFunc::BvNot => "bvnot",
                ThyFunc::BvAdd => "bvadd",
                ThyFunc::BvNeg => "bvneg",
                ThyFunc::BvSub => "bvsub",
                ThyFunc::BvMul => "bvmul",
                ThyFunc::BvShl => "bvshl",
                ThyFunc::BvUgt => "bvugt",
                ThyFunc::BvSgt => "bvsgt",
                ThyFunc::BvUlt => "bvult",
                ThyFunc::BvSlt => "bvslt",
                ThyFunc::SetEmpty => "as emptyset",
                ThyFunc::SetSng => "singleton",
                ThyFunc::SetCup => "union",
                ThyFunc::SetCap => "intersection",
                ThyFunc::SetDif => "setminus",
                ThyFunc::SetMem => "member",
                ThyFunc::SetSub => "subset",
                ThyFunc::MapDefault => "const",
                ThyFunc::MapSelect => "select",
                ThyFunc::MapStore => "store",
                _ => unreachable!(),
            };
            write!(f, "{name}")
        }
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

fn fmt_const_decl<T: Types>(
    decl: &ConstDecl<T>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
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
