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
    time::{Duration, Instant},
};

use crate::{
    Error, FixpointResult, FixpointStatus, KVarBind, Stats, Task, Types,
    format_smt::{SmtFormatter, collect_tagged_heads},
    sexp,
};

/// Complete output of a Hornspec invocation, including information omitted from
/// the common fixpoint result representation.
#[derive(serde::Serialize)]
pub struct HornspecOutput<Tag> {
    #[serde(skip)]
    pub result: FixpointResult<Tag>,
    #[serde(skip)]
    pub duration: Duration,
    pub status: String,
    #[serde(skip)]
    pub stdout: String,
    #[serde(skip)]
    pub stderr: String,
    pub exit_code: Option<i32>,
    pub error: Option<String>,
    pub timeout_ms: u64,
    pub skip_maximal: bool,
    pub command: Vec<String>,
    pub definitions: Vec<HornspecDefinition>,
}

#[derive(serde::Serialize)]
pub struct HornspecDefinition {
    pub name: String,
    pub parameters: Vec<HornspecParameter>,
    pub return_sort: String,
    pub body_smtlib: String,
    pub declaration_smtlib: String,
}

#[derive(serde::Serialize)]
pub struct HornspecParameter {
    pub name: String,
    pub sort: String,
}

/// Run hornspec on the given task and parse the output.
pub(crate) fn run_hornspec<T: Types>(task: &Task<T>) -> io::Result<FixpointResult<T::Tag>> {
    Ok(run_hornspec_with_output(task)?.result)
}

pub(crate) fn run_hornspec_with_output<T: Types>(
    task: &Task<T>,
) -> io::Result<HornspecOutput<T::Tag>> {
    let timeout_seconds = flux_config::hornspec_timeout();
    let skip_maximal = flux_config::hornspec_skip_maximal();
    let mut command =
        vec!["timeout".to_owned(), format!("{timeout_seconds}s"), "hornspec".to_owned()];
    if skip_maximal {
        command.push("--skip-maximal".to_owned());
    }
    command.push("-".to_owned());
    let start = Instant::now();
    // Spawn hornspec binary, piping input via stdin
    let mut child = Command::new(&command[0])
        .args(&command[1..])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let mut stdin = None;
    std::mem::swap(&mut stdin, &mut child.stdin);
    let input_result = {
        let mut w = BufWriter::new(stdin.unwrap());
        writeln!(&mut w, "{}", SmtFormatter(task)).and_then(|()| w.flush())
    };

    let output = child.wait_with_output()?;
    let duration = start.elapsed();
    // Always reap the child, including early solver exits causing a broken pipe.
    if let Err(error) = input_result
        && error.kind() != io::ErrorKind::BrokenPipe
    {
        return Err(error);
    }
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    if matches!(output.status.code(), Some(125..=127)) {
        return Err(io::Error::other(format!("failed to launch Hornspec: {stderr}")));
    }

    let (status, error) =
        classify_output(output.status.success(), output.status.code(), &stdout, &stderr);
    let result = if status == "timeout" {
        FixpointResult {
            status: FixpointStatus::Timeout,
            solution: vec![],
            non_cuts_solution: vec![],
        }
    } else {
        parse_hornspec_output(if status == "unknown" { "unknown" } else { &stdout }, task)?
    };
    let mut definitions = vec![];
    if let Some((_, rest)) = stdout.trim().split_once('\n') {
        let mut parser = sexp::Parser::new(rest);
        while let Ok(sexpr) = parser.parse() {
            if let Some(definition) = parse_definition(&sexpr) {
                definitions.push(definition);
            }
        }
    }
    Ok(HornspecOutput {
        result,
        duration,
        status,
        stdout,
        stderr,
        exit_code: output.status.code(),
        error,
        timeout_ms: timeout_seconds * 1000,
        skip_maximal,
        command,
        definitions,
    })
}

fn classify_output(
    success: bool,
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
) -> (String, Option<String>) {
    if exit_code == Some(124) {
        return ("timeout".into(), None);
    }
    if !success {
        return (
            "unknown".into(),
            Some(format!(
                "Hornspec exited with {exit_code:?}: {}",
                stderr.trim().chars().take(1000).collect::<String>()
            )),
        );
    }
    let status = stdout.split_whitespace().next().unwrap_or_default();
    if matches!(status, "unsat" | "sat" | "unknown") {
        (status.into(), None)
    } else {
        ("unknown".into(), Some(format!("unexpected Hornspec output status: {status:?}")))
    }
}

fn parse_definition(sexpr: &sexp::Sexp) -> Option<HornspecDefinition> {
    let bind = parse_single_define_fun(sexpr)?;
    let sexp::Sexp::List(items) = sexpr else { return None };
    let sexp::Sexp::List(parameters) = &items[2] else { return None };
    let parameters = parameters
        .iter()
        .map(|parameter| {
            let sexp::Sexp::List(pair) = parameter else { return None };
            let [name, sort] = pair.as_slice() else { return None };
            Some(HornspecParameter { name: format_sexp(name), sort: format_sexp(sort) })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(HornspecDefinition {
        name: bind.kvar,
        parameters,
        return_sort: format_sexp(&items[3]),
        body_smtlib: bind.val,
        declaration_smtlib: format_sexp(sexpr),
    })
}

/// Parse hornspec output into a FixpointResult.
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
) -> io::Result<FixpointResult<T::Tag>> {
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
            Ok(FixpointResult {
                status: FixpointStatus::Safe(Stats::default()),
                solution,
                non_cuts_solution: vec![],
            })
        }
        "sat" | "unknown" => {
            // NOTE(CK): We'll treat unknown as a failure too.

            // sat means unsafe — the CHC system has no solution
            // Collect all tagged concrete heads as errors (conservative)
            let tagged_heads = collect_tagged_heads(&task.constraint);
            let errors: Vec<Error<T::Tag>> = tagged_heads
                .into_iter()
                .enumerate()
                .map(|(i, tag)| Error { id: i as i32, tag })
                .collect();
            Ok(FixpointResult {
                status: FixpointStatus::Unsafe(Stats::default(), errors),
                solution: vec![],
                non_cuts_solution: vec![],
            })
        }
        _ => Err(io::Error::other(format!("unexpected hornspec output status: {status_str}"))),
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

    Some(KVarBind { kvar: name.clone(), val: body_str })
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn definition_preserves_parameter_order_sorts_and_body() {
        let input = "(define-fun wk$foo$0 ((x Int) (b Bool)) Bool (and (> x 0) b))";
        let sexpr = sexp::Parser::new(input).parse().unwrap();
        let definition = parse_definition(&sexpr).unwrap();
        assert_eq!(definition.name, "wk$foo$0");
        assert_eq!(definition.parameters.len(), 2);
        assert_eq!(definition.parameters[0].name, "x");
        assert_eq!(definition.parameters[0].sort, "Int");
        assert_eq!(definition.parameters[1].name, "b");
        assert_eq!(definition.parameters[1].sort, "Bool");
        assert_eq!(definition.return_sort, "Bool");
        assert_eq!(definition.body_smtlib, "(and (> x 0) b)");
        assert_eq!(definition.declaration_smtlib, input);
    }

    #[test]
    fn output_serialization_excludes_raw_artifacts_and_internal_result() {
        let output = HornspecOutput::<String> {
            result: FixpointResult {
                status: FixpointStatus::Timeout,
                solution: vec![],
                non_cuts_solution: vec![],
            },
            duration: Duration::from_secs(5),
            status: "timeout".into(),
            stdout: "large stdout".into(),
            stderr: "large stderr".into(),
            exit_code: Some(124),
            error: None,
            timeout_ms: 5_000,
            skip_maximal: true,
            command: vec![],
            definitions: vec![],
        };
        let json = serde_json::to_value(output).unwrap();
        assert_eq!(json["status"], "timeout");
        assert_eq!(json["exit_code"], 124);
        for omitted in ["stdout", "stderr", "result", "duration"] {
            assert!(json.get(omitted).is_none());
        }
    }

    #[test]
    fn solver_crashes_are_unknown_even_with_partial_safe_output() {
        for stdout in ["", "unsat\n(define-fun p () Bool true)"] {
            let (status, error) =
                classify_output(false, Some(134), stdout, "Assertion `0' failed.");
            assert_eq!(status, "unknown");
            assert!(error.unwrap().contains("Assertion `0' failed."));
        }
        assert_eq!(classify_output(false, None, "", "killed").0, "unknown");
        assert_eq!(classify_output(false, Some(124), "", "").0, "timeout");
        assert_eq!(classify_output(true, Some(0), "unsat\n", "").0, "unsat");
    }
}
