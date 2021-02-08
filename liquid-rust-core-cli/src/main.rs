use std::{
    env,
    fs::File,
    io::{prelude::*, BufReader},
};

use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    files::SimpleFile,
    term::{
        self,
        termcolor::{ColorChoice, StandardStream},
    },
};
use lalrpop_util::lalrpop_mod;
use liquid_rust_typeck::check_program;
lalrpop_mod!(
    #[allow(clippy::all, clippy::pedantic)]
    pub grammar
);
type ParseError<'input> = lalrpop_util::ParseError<usize, grammar::Token<'input>, &'input str>;

fn main() -> Result<(), codespan_reporting::files::Error> {
    let args: Vec<_> = env::args().collect();
    let mut buf_reader = BufReader::new(File::open(&args[1])?);
    let mut contents = String::new();
    buf_reader.read_to_string(&mut contents)?;

    let file = SimpleFile::new(&args[1], &contents);

    let program = match grammar::ProgramParser::new().parse(&contents) {
        Ok(program) => program,
        Err(err) => {
            diagnostics(&file, err)?;
            return Ok(());
        }
    };

    check_program(program);
    Ok(())
}

fn diagnostics(
    file: &SimpleFile<&String, &String>,
    err: ParseError,
) -> Result<(), codespan_reporting::files::Error> {
    use lalrpop_util::ParseError::*;
    let diagnostic: Diagnostic<()> = match err {
        User { error } => Diagnostic::error().with_message(error.to_string()),

        InvalidToken { location } => Diagnostic::error()
            .with_message("Invalid token")
            .with_labels(vec![Label::primary((), location..location)]),

        UnrecognizedEOF { location, expected } => Diagnostic::error()
            .with_message("Unrecognized EOF")
            .with_labels(vec![
                Label::primary((), location..location).with_message(fmt_expected(&expected))
            ]),

        UnrecognizedToken {
            token: (start, token, end),
            expected,
        } => Diagnostic::error()
            .with_message(format!("Unrecognized token `{}`", token,))
            .with_labels(vec![
                Label::primary((), start..end).with_message(fmt_expected(&expected))
            ]),

        ExtraToken {
            token: (start, token, end),
        } => Diagnostic::error()
            .with_message(format!("Extra token `{}`", token,))
            .with_labels(vec![Label::primary((), start..end)]),
    };
    let writer = StandardStream::stderr(ColorChoice::Always);
    let config = codespan_reporting::term::Config::default();
    let mut lock = writer.lock();

    term::emit(&mut lock, &config, file, &diagnostic)
}

fn fmt_expected(expected: &[String]) -> String {
    let mut s = String::new();
    if !expected.is_empty() {
        for (i, e) in expected.iter().enumerate() {
            let sep = match i {
                0 => "Expected one of",
                _ if i < expected.len() - 1 => ",",
                _ => " or",
            };
            s.push_str(&format!("{} {}", sep, e));
        }
    }
    s
}
