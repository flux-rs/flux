/// Runner and output parser for the hornspec binary.
///
/// Hornspec is a CHC (Constrained Horn Clause) solver. It takes CHC problems in
/// either Datalog or SMT-LIB HORN format and returns solutions for unknown predicates.
///
/// The output format is:
/// ```text
/// unsat
/// (define-fun h ((_FH_0 Int)) Bool
///   true)
/// (define-fun f ((_FH_1 Int)) Bool
///   true)
/// ```
///
/// Where `unsat` means the system is safe (no violation found) and `sat` means unsafe.
use std::{
    io::{self, BufWriter, Write},
    process::{Command, Stdio},
};

use crate::{
    Backend, Error, FixpointStatus, KVarBind, LeanStatus, Stats, Task, Types,
    VerificationResult,
    format_smt::{collect_tagged_heads, task_to_smt_string},
    sexp,
};

/// Run hornspec on the given task and parse the output.
pub(crate) fn run_hornspec<T: Types>(task: &Task<T>) -> io::Result<VerificationResult<T::Tag>> {
    // Format the task in the SMT-LIB HORN CHC format
    let input = match task.backend {
        Backend::Hornspec => task_to_smt_string(task),
        Backend::Fixpoint => unreachable!("run_hornspec called with Fixpoint backend"),
    };

    // Spawn hornspec binary, piping input via stdin
    let mut child = Command::new("hornspec")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let mut stdin = None;
    std::mem::swap(&mut stdin, &mut child.stdin);
    {
        let mut w = BufWriter::new(stdin.unwrap());
        w.write_all(input.as_bytes())?;
    }

    let output = child.wait_with_output()?;

    if !output.status.success() && output.stdout.is_empty() {
        let stderr = std::str::from_utf8(&output.stderr)
            .unwrap_or("hornspec exited with a non-zero return code");
        return Err(io::Error::other(stderr));
    }

    let stdout = std::str::from_utf8(&output.stdout)
        .map_err(|e| io::Error::other(format!("hornspec output is not valid UTF-8: {e}")))?;

    parse_hornspec_output(stdout, task)
}

/// Parse hornspec output into a VerificationResult.
///
/// The output has the form:
/// ```text
/// unsat
/// (define-fun name ((param Sort)) Bool body)
/// ...
/// ```
/// or simply:
/// ```text
/// sat
/// ```
fn parse_hornspec_output<T: Types>(
    output: &str,
    task: &Task<T>,
) -> io::Result<VerificationResult<T::Tag>> {
    let output = output.trim();

    // The first line/word is the status
    let (status_str, rest) = match output.split_once('\n') {
        Some((first, rest)) => (first.trim(), rest.trim()),
        None => (output, ""),
    };

    match status_str {
        "unsat" => {
            // unsat means safe — the CHC system has a solution
            let solution = parse_define_funs(rest)?;
            Ok(VerificationResult {
                status: FixpointStatus::Safe(Stats::default()),
                solution,
                non_cuts_solution: vec![],
                lean_status: LeanStatus::default(),
            })
        }
        "sat" => {
            // sat means unsafe — the CHC system has no solution
            // Collect all tagged concrete heads as errors (conservative)
            let tagged_heads = collect_tagged_heads(&task.constraint);
            let errors: Vec<Error<T::Tag>> = tagged_heads
                .into_iter()
                .enumerate()
                .map(|(i, tag)| Error { id: i as i32, tag })
                .collect();
            Ok(VerificationResult {
                status: FixpointStatus::Unsafe(Stats::default(), errors),
                solution: vec![],
                non_cuts_solution: vec![],
                lean_status: LeanStatus::default(),
            })
        }
        "unknown" => {
            Ok(VerificationResult {
                status: FixpointStatus::Crash(crate::CrashInfo(vec![
                    serde_json::Value::String("hornspec returned unknown".to_string()),
                ])),
                solution: vec![],
                non_cuts_solution: vec![],
                lean_status: LeanStatus::default(),
            })
        }
        _ => {
            Err(io::Error::other(format!(
                "unexpected hornspec output status: {status_str}"
            )))
        }
    }
}

/// Parse `(define-fun ...)` declarations from hornspec output into KVarBind values.
fn parse_define_funs(input: &str) -> io::Result<Vec<KVarBind>> {
    if input.is_empty() {
        return Ok(vec![]);
    }

    let mut binds = Vec::new();
    let mut parser = sexp::Parser::new(input);

    while let Ok(sexpr) = parser.parse() {
        if let Some(bind) = parse_single_define_fun(&sexpr) {
            binds.push(bind);
        }
    }

    Ok(binds)
}

/// Parse a single `(define-fun name ((params)) Bool body)` S-expression.
fn parse_single_define_fun(sexpr: &sexp::Sexp) -> Option<KVarBind> {
    let sexp::Sexp::List(items) = sexpr else {
        return None;
    };

    // Must start with `define-fun`
    if items.len() < 5 {
        return None;
    }

    let sexp::Sexp::Atom(sexp::Atom::S(keyword)) = &items[0] else {
        return None;
    };
    if keyword != "define-fun" {
        return None;
    }

    // Second element is the function name
    let sexp::Sexp::Atom(sexp::Atom::S(name)) = &items[1] else {
        return None;
    };

    // The body is the last element — format it back as a string
    let body = &items[items.len() - 1];
    let body_str = format_sexp(body);

    Some(KVarBind {
        kvar: name.clone(),
        val: body_str,
    })
}

/// Format an S-expression back to a string representation.
fn format_sexp(sexp: &sexp::Sexp) -> String {
    match sexp {
        sexp::Sexp::Atom(atom) => format_atom(atom),
        sexp::Sexp::List(items) => {
            let inner: Vec<String> = items.iter().map(format_sexp).collect();
            format!("({})", inner.join(" "))
        }
    }
}

fn format_atom(atom: &sexp::Atom) -> String {
    match atom {
        sexp::Atom::S(s) => s.clone(),
        sexp::Atom::Q(s) => format!("\"{s}\""),
        sexp::Atom::I(i) => i.to_string(),
        sexp::Atom::F(f) => f.to_string(),
        sexp::Atom::B(b) => b.to_string(),
    }
}
