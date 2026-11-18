//! Running Flux on a program: `cargo x run <file> -- -Fdump-checker-trace=debug` from the
//! repository root, so Flux and its sysroot are rebuilt when needed, exactly as on the command
//! line. It produces the trace and the diagnostics.

use std::{
    io::{BufRead, BufReader},
    path::Path,
    process::Stdio,
    sync::LazyLock,
    time::{Duration, Instant},
};

use regex::Regex;
use tokio::{
    process::Command,
    sync::{Mutex, mpsc::UnboundedSender},
};

use crate::protocol::{RunResult, Stage};

/// The program's file name, as shown in the output instead of its temporary path.
const SRC_NAME: &str = "input.rs";
/// Generous, because a run may first rebuild Flux and its sysroot.
const TIMEOUT: Duration = Duration::from_secs(900);
/// cargo's progress lines (`Compiling ...`, `Finished ...`), which would bury Flux's diagnostics.
/// Color escapes, which Flux prints even with `--color=never`.
static ANSI_ESCAPE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"\x1b\[[0-9;]*m").unwrap());
static CARGO_PROGRESS: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^\s*(Compiling|Checking|Finished|Running|Blocking|Fresh|Updating|Downloaded?|Locking|Adding)\b")
        .unwrap()
});

/// `cargo x run` copies the sysroot, and concurrent runs clash doing that: one run at a time.
static RUN_LOCK: Mutex<()> = Mutex::const_new(());

/// Variables `cargo run` sets for blick itself. They would leak into the `cargo x run`
/// started here and make it see the wrong package or toolchain.
fn is_outer_cargo_var(k: &str) -> bool {
    matches!(
        k,
        "CARGO"
            | "CARGO_MANIFEST_DIR"
            | "CARGO_MANIFEST_PATH"
            | "CARGO_CRATE_NAME"
            | "CARGO_BIN_NAME"
            | "CARGO_PRIMARY_PACKAGE"
            | "RUSTUP_TOOLCHAIN"
            | "RUST_RECURSION_COUNT"
    ) || k.starts_with("CARGO_PKG_")
}

/// Runs Flux on `source` from the repository at `repo`. Every output line is sent to `lines` as
/// it is printed. Dropping the future stops the run.
pub async fn run(
    repo: &Path,
    source: &str,
    extra_flags: &[String],
    lines: &UnboundedSender<String>,
) -> anyhow::Result<RunResult> {
    let _guard = match RUN_LOCK.try_lock() {
        Ok(guard) => guard,
        Err(_) => {
            let _ = lines.send("[waiting for another run to finish]".to_string());
            RUN_LOCK.lock().await
        }
    };
    let tmp = tempfile::Builder::new().prefix("flux-trace-").tempdir()?;
    let src = tmp.path().join(SRC_NAME);
    std::fs::write(&src, source)?;
    let src_str = src.to_string_lossy().into_owned();
    let log_dir = tmp.path().join("log");
    let mut args: Vec<String> = vec![
        "x".into(),
        "run".into(),
        src_str.clone(),
        "--".into(),
        "--color=never".into(),
        "-Fdump-checker-trace=debug".into(),
        format!("-Flog-dir={}", log_dir.display()),
    ];
    args.extend(extra_flags.iter().cloned());
    let shown = |s: &str| {
        ANSI_ESCAPE
            .replace_all(&s.replace(&src_str, SRC_NAME), "")
            .into_owned()
    };
    let _ = lines.send(shown(&format!("$ cargo {}", args.join(" "))));

    let start = Instant::now();
    // stderr into stdout, so the lines arrive in the order they were printed
    let (reader, writer) = std::io::pipe()?;
    let mut child = {
        let mut cmd = Command::new("cargo");
        cmd.args(&args)
            .current_dir(repo)
            .stdin(Stdio::null())
            .stdout(writer.try_clone()?)
            .stderr(writer)
            .env("CARGO_TERM_COLOR", "never")
            .kill_on_drop(true);
        for (k, _) in std::env::vars_os() {
            if let Some(k) = k.to_str()
                && is_outer_cargo_var(k)
            {
                cmd.env_remove(k);
            }
        }
        // `cmd` is dropped here, closing our ends of the pipe's write side
        cmd.spawn()?
    };

    let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<String>();
    tokio::task::spawn_blocking(move || {
        for line in BufReader::new(reader).split(b'\n') {
            let Ok(line) = line else { break };
            if tx
                .send(String::from_utf8_lossy(&line).into_owned())
                .is_err()
            {
                break;
            }
        }
    });

    let mut collected = Vec::new();
    let finished = tokio::time::timeout(TIMEOUT, async {
        while let Some(line) = rx.recv().await {
            let _ = lines.send(shown(&line));
            collected.push(line);
        }
        child.wait().await
    })
    .await;
    let code = match finished {
        Ok(status) => Some(status?.code().unwrap_or(-1)),
        Err(_) => {
            let _ = child.kill().await;
            collected.push(format!("[timed out after {}s]", TIMEOUT.as_secs()));
            None
        }
    };
    let elapsed = (start.elapsed().as_secs_f64() * 100.0).round() / 100.0;
    let trace = std::fs::read(log_dir.join("checker"))
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .unwrap_or_default();

    // xtask echoes each command it runs as `$ ...`; the last one is Flux on the program. Show only
    // what that printed, unless the run never got there (a build error), then show everything.
    let mut flux_runs = collected
        .iter()
        .enumerate()
        .filter(|(_, l)| l.starts_with("$ ") && l.contains("flux-driver") && !l.contains("cargo "))
        .map(|(i, _)| i);
    let (stage, out): (Stage, Vec<&str>) = match flux_runs.next_back() {
        Some(i) => {
            (
                Stage::Flux,
                collected[i + 1..]
                    .iter()
                    .map(String::as_str)
                    .filter(|l| !l.starts_with("Error: command exited with"))
                    .collect(),
            )
        }
        None => {
            (
                if matches!(code, Some(c) if c != 0) { Stage::Build } else { Stage::Flux },
                collected
                    .iter()
                    .map(String::as_str)
                    .filter(|l| !CARGO_PROGRESS.is_match(l))
                    .collect(),
            )
        }
    };
    Ok(RunResult {
        ok: code == Some(0),
        exit: code,
        stage,
        stderr: shown(out.join("\n").trim_matches('\n')),
        trace,
        elapsed: Some(elapsed),
    })
}
