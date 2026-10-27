//! Subprocess for interfacing with Z3. We only added enough features to support
//! [`suggestion_solver.rs`]

use std::{
    io::{self, BufRead, BufReader, Read as _, Write as _},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    sync::{Arc, Mutex},
    thread::JoinHandle,
};

use crate::sexp::{Atom, Parser, Sexp};

#[derive(Debug)]
pub(crate) enum Z3Error {
    Io(io::Error),
    Timeout,
}

impl From<io::Error> for Z3Error {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SatStatus {
    Sat,
    Unsat,
    Unknown,
}

struct Response {
    stdout: String,
    stderr: String,
}

pub(crate) struct Z3Subprocess {
    child: Child,
    stdin: Option<ChildStdin>,
    stdout: BufReader<ChildStdout>,
    stderr: Arc<Mutex<Vec<u8>>>,
    stderr_reader: Option<JoinHandle<()>>,
    request_id: usize,
}

impl Z3Subprocess {
    pub(crate) fn new() -> io::Result<Self> {
        let mut child = Command::new("z3")
            .args(["-smt2", "-in"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        let stdin = child.stdin.take().expect("Z3 stdin is piped");
        let stdout = child.stdout.take().expect("Z3 stdout is piped");
        let mut child_stderr = child.stderr.take().expect("Z3 stderr is piped");
        let stderr = Arc::new(Mutex::new(Vec::new()));
        let stderr_buf = Arc::clone(&stderr);
        let stderr_reader = std::thread::spawn(move || {
            let mut chunk = [0; 4096];
            loop {
                match child_stderr.read(&mut chunk) {
                    Ok(0) | Err(_) => break,
                    Ok(len) => stderr_buf.lock().unwrap().extend_from_slice(&chunk[..len]),
                }
            }
        });
        Ok(Self {
            child,
            stdin: Some(stdin),
            stdout: BufReader::new(stdout),
            stderr,
            stderr_reader: Some(stderr_reader),
            request_id: 0,
        })
    }

    fn request(&mut self, commands: &str) -> io::Result<Response> {
        let marker = format!("__flux_z3_end_{}__", self.request_id);
        self.request_id += 1;
        self.stderr.lock().unwrap().clear();
        let stdin = self.stdin.as_mut().expect("Z3 stdin is open");
        writeln!(stdin, "{commands}")?;
        writeln!(stdin, "(echo \"{marker}\")")?;
        stdin.flush()?;

        // Use a marker to find the end of Z3's output.
        let mut response = String::new();
        loop {
            let mut line = String::new();
            match self.stdout.read_line(&mut line)? {
                0 => {
                    let status = self.child.try_wait()?.and_then(|status| status.code());
                    let stderr = self.take_stderr();
                    panic!(
                        "Z3 closed stdout before the response marker (status {status:?}); stdout: {response:?}; stderr: {stderr:?}"
                    );
                }
                _ if line.trim() == marker => {
                    return Ok(Response { stdout: response, stderr: self.take_stderr() });
                }
                _ => response.push_str(&line),
            }
        }
    }

    fn execute(&mut self, commands: &str) -> io::Result<()> {
        let Response { stdout, stderr } = self.request(commands)?;
        assert!(
            stdout.trim().is_empty(),
            "unexpected Z3 setup response; commands: {commands:?}; stdout: {stdout:?}; stderr: {stderr:?}"
        );
        Ok(())
    }

    /// Check satisfiability (setup is a string that is sent to Z3 to be done
    /// before the check)
    pub(crate) fn check_sat(&mut self, setup: &str) -> Result<SatStatus, Z3Error> {
        let Response { stdout, stderr } =
            self.request(&format!("(push)\n{setup}\n(check-sat)\n(pop)"))?;
        match stdout.trim() {
            "sat" => Ok(SatStatus::Sat),
            "unsat" => Ok(SatStatus::Unsat),
            "unknown" => Ok(SatStatus::Unknown),
            _ if is_timeout(&stdout) => Err(Z3Error::Timeout),
            _ => panic!("unexpected Z3 status response; stdout: {stdout:?}; stderr: {stderr:?}"),
        }
    }

    /// Apply a tactic (as a string) under a context (setup), returning the
    /// parsed formulas in each resulting goal.
    pub(crate) fn apply(&mut self, setup: &str, tactic: &str) -> Result<Vec<Vec<Sexp>>, Z3Error> {
        let Response { stdout, stderr } =
            self.request(&format!("(push)\n{setup}\n(apply {tactic})\n(pop)"))?;
        if is_timeout(&stdout) {
            return Err(Z3Error::Timeout);
        }
        Ok(parse_goals(&stdout, &stderr))
    }

    pub(crate) fn scoped<R, E>(
        &mut self,
        setup: &str,
        f: impl FnOnce(&mut Self) -> Result<R, E>,
    ) -> Result<R, E>
    where
        E: From<Z3Error> + From<io::Error>,
    {
        self.execute(&format!("(push)\n{setup}"))?;
        let result = f(self);
        let pop = self.execute("(pop)");
        match result {
            Err(err) => Err(err),
            Ok(value) => pop.map(|_| value).map_err(E::from),
        }
    }

    pub(crate) fn reset(&mut self, declarations: &str) -> io::Result<()> {
        self.execute(&format!("(reset)\n{declarations}"))
    }

    fn take_stderr(&self) -> String {
        let bytes = std::mem::take(&mut *self.stderr.lock().unwrap());
        String::from_utf8_lossy(&bytes).into_owned()
    }
}

impl Drop for Z3Subprocess {
    fn drop(&mut self) {
        self.stdin.take();
        let _ = self.child.wait();
        if let Some(reader) = self.stderr_reader.take() {
            let _ = reader.join();
        }
    }
}

fn is_timeout(stdout: &str) -> bool {
    let output = stdout.trim().to_ascii_lowercase();
    // This is to the best of my understanding what Z3 outputs.
    output.starts_with("(error ") && output.contains("canceled")
}

fn parse_goals(stdout: &str, stderr: &str) -> Vec<Vec<Sexp>> {
    let parsed = Parser::new(stdout).parse_all().unwrap_or_else(|err| {
        panic!("failed to parse Z3 goals response: {err:?}; stdout: {stdout:?}; stderr: {stderr:?}")
    });
    let [Sexp::List(items)] = parsed.as_slice() else {
        panic!("expected one `(goals ...)` response; stdout: {stdout:?}; stderr: {stderr:?}");
    };
    if atom_symbol(items.first()) != Some("goals") {
        panic!(
            "Z3 goals response does not start with `goals`; stdout: {stdout:?}; stderr: {stderr:?}"
        );
    }
    items[1..]
        .iter()
        .map(|goal| {
            let Sexp::List(entries) = goal else {
                panic!("Z3 goal response entry is not a list; entry: {goal:?}; stdout: {stdout:?}; stderr: {stderr:?}");
            };
            if atom_symbol(entries.first()) != Some("goal") {
                panic!("expected `(goal ...)` in Z3 goals response; entry: {goal:?}; stdout: {stdout:?}; stderr: {stderr:?}");
            }
            let metadata = entries[1..]
                .iter()
                .position(|entry| {
                    atom_symbol(Some(entry)).is_some_and(|name| name.starts_with(':'))
                })
                .unwrap_or(entries.len() - 1);
            entries[1..1 + metadata].to_vec()
        })
        .collect()
}

fn atom_symbol(sexp: Option<&Sexp>) -> Option<&str> {
    match sexp {
        Some(Sexp::Atom(Atom::S(symbol))) => Some(symbol),
        _ => None,
    }
}
