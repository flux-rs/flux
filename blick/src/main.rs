//! Serves Blick and runs Flux on programs pasted into it.
//!
//!     cargo run -p blick [-- --port 8765]
//!
//! Then open http://127.0.0.1:8765. On startup, blick installs the client's npm packages
//! when they are missing or out of date (`npm ci`), and starts `vite build --watch` on the client,
//! which rebuilds `client/dist` whenever a source file changes. The page reloads after each
//! rebuild. It needs Node.js and npm.
//!
//! - `GET /api/info`: `{command, repo}`, shown in the page's status line.
//! - `GET /api/run-ws` (WebSocket): the page sends `{source, flags}`; the server streams every
//!   output line as `{"type": "line", "text": ...}` while `cargo x run` works, then sends
//!   `{"type": "done", ...result}` and closes. See `run.rs`.
//! - `GET /api/reload` (WebSocket): the server sends `reload` after the client was rebuilt.
//! - Everything else is a file of `client/dist`.
//!
//! The server compiles whatever it is sent, so it only listens on localhost.

mod protocol;
mod run;

use std::{
    net::{Ipv4Addr, SocketAddr},
    path::{Path, PathBuf},
    process::Stdio,
    time::Duration,
};

use anyhow::{Context, bail};
use axum::{
    Json, Router,
    extract::{
        State,
        ws::{Message, WebSocket, WebSocketUpgrade},
    },
    http::{HeaderValue, header},
    response::Response,
    routing::get,
};
use clap::Parser;
use notify::{RecursiveMode, Watcher};
use protocol::{Info, RunRequest, RunResult, ServerMsg};
use tokio::{
    process::{Child, Command},
    sync::broadcast,
};
use tower_http::{services::ServeDir, set_header::SetResponseHeaderLayer};

#[derive(Parser)]
#[command(about = "Run Flux on programs and explore its checker trace in the browser")]
struct Args {
    /// The port to listen on (on 127.0.0.1).
    #[arg(long, default_value_t = 8765)]
    port: u16,
}

#[derive(Clone)]
struct App {
    repo: PathBuf,
    /// Fires after the client was rebuilt.
    reload: broadcast::Sender<()>,
}

const CRATE_DIR: &str = env!("CARGO_MANIFEST_DIR");

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let crate_dir = Path::new(CRATE_DIR);
    let repo = crate_dir.parent().unwrap().to_path_buf();
    let client = crate_dir.join("client");
    let dist = client.join("dist");

    protocol::write_bindings(&client.join("src/bindings"))?;
    install_client_deps(&client)?;

    let (reload, mut first_build) = broadcast::channel(16);
    std::fs::create_dir_all(&dist)?;
    let _watcher = watch_dist(&dist, reload.clone())?;
    let mut vite = start_vite(&client)?;
    // Serve once the first build is written (or failed: vite keeps watching and says why).
    tokio::select! {
        _ = first_build.recv() => {}
        status = vite.wait() => bail!("vite exited ({})", status?),
        _ = tokio::time::sleep(Duration::from_secs(60)) => {}
    }

    let app = App { repo, reload };
    let router = Router::new()
        .route("/api/info", get(info))
        .route("/api/run-ws", get(run_ws))
        .route("/api/reload", get(reload_ws))
        .fallback_service(ServeDir::new(&dist))
        .layer(SetResponseHeaderLayer::overriding(
            header::CACHE_CONTROL,
            HeaderValue::from_static("no-store"),
        ))
        .with_state(app);

    let addr = SocketAddr::from((Ipv4Addr::LOCALHOST, args.port));
    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .with_context(|| format!("cannot listen on {addr}"))?;
    eprintln!("\nblick: http://{addr}\n");
    axum::serve(listener, router)
        .with_graceful_shutdown(shutdown_signal())
        .await?;
    let _ = vite.kill().await;
    Ok(())
}

/// Ctrl+C, `kill`, or the terminal going away. Any of them must stop vite too (below), so it is
/// not left watching on its own.
async fn shutdown_signal() {
    use tokio::signal::unix::{SignalKind, signal};
    let mut term = signal(SignalKind::terminate()).expect("installing a SIGTERM handler");
    let mut hup = signal(SignalKind::hangup()).expect("installing a SIGHUP handler");
    tokio::select! {
        _ = tokio::signal::ctrl_c() => {}
        _ = term.recv() => {}
        _ = hup.recv() => {}
    }
}

/// Runs `npm ci` when the installed packages are not the ones `package-lock.json` asks for. The
/// lockfile of the last install is kept in `node_modules` to tell.
fn install_client_deps(client: &Path) -> anyhow::Result<()> {
    let lock = std::fs::read(client.join("package-lock.json"))
        .context("reading client/package-lock.json")?;
    let stamp = client.join("node_modules/.blick-lock");
    if std::fs::read(&stamp).ok().as_ref() == Some(&lock) {
        return Ok(());
    }
    eprintln!("Installing the client's packages (npm ci)...");
    let status = std::process::Command::new("npm")
        .arg("ci")
        .current_dir(client)
        .status()
        .map_err(|err| {
            if err.kind() == std::io::ErrorKind::NotFound {
                anyhow::anyhow!("npm not found: blick needs Node.js and npm (https://nodejs.org)")
            } else {
                anyhow::anyhow!("running npm: {err}")
            }
        })?;
    if !status.success() {
        bail!("npm ci failed ({status})");
    }
    std::fs::write(&stamp, lock)?;
    Ok(())
}

fn start_vite(client: &Path) -> anyhow::Result<Child> {
    Command::new(client.join("node_modules/.bin/vite"))
        .args(["build", "--watch", "--logLevel", "warn"])
        .current_dir(client)
        .stdin(Stdio::null())
        .kill_on_drop(true)
        .spawn()
        .context("starting vite")
}

/// Fires `reload` once `dist` has been quiet for a moment after a change: a build replaces all of
/// its files.
fn watch_dist(dist: &Path, reload: broadcast::Sender<()>) -> anyhow::Result<impl Watcher> {
    let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel();
    let mut watcher = notify::recommended_watcher(move |ev: notify::Result<notify::Event>| {
        if ev.is_ok_and(|ev| !ev.kind.is_access()) {
            let _ = tx.send(());
        }
    })?;
    watcher.watch(dist, RecursiveMode::Recursive)?;
    let index = dist.join("index.html");
    tokio::spawn(async move {
        while rx.recv().await.is_some() {
            while let Ok(Some(())) =
                tokio::time::timeout(Duration::from_millis(300), rx.recv()).await
            {}
            if index.exists() {
                eprintln!("client rebuilt");
                let _ = reload.send(());
            }
        }
    });
    Ok(watcher)
}

async fn info(State(app): State<App>) -> Json<Info> {
    Json(Info { command: "cargo x run".into(), repo: app.repo.display().to_string() })
}

async fn reload_ws(State(app): State<App>, ws: WebSocketUpgrade) -> Response {
    let mut rx = app.reload.subscribe();
    ws.on_upgrade(move |mut socket| {
        async move {
            loop {
                tokio::select! {
                    ev = rx.recv() => {
                        if ev.is_err() || socket.send(Message::Text("reload".into())).await.is_err() {
                            break;
                        }
                    }
                    msg = socket.recv() => if !matches!(msg, Some(Ok(_))) { break },
                }
            }
        }
    })
}

async fn run_ws(State(app): State<App>, ws: WebSocketUpgrade) -> Response {
    ws.on_upgrade(move |socket| handle_run(socket, app))
}

async fn send(socket: &mut WebSocket, msg: &ServerMsg) -> bool {
    let text = serde_json::to_string(msg).expect("messages serialize");
    socket.send(Message::Text(text.into())).await.is_ok()
}

async fn handle_run(mut socket: WebSocket, app: App) {
    let req = match socket.recv().await {
        Some(Ok(Message::Text(text))) => {
            serde_json::from_str::<RunRequest>(&text).map_err(|e| e.to_string())
        }
        _ => Err("bad request".to_string()),
    };
    let req = match req {
        Ok(req) => req,
        Err(err) => {
            send(&mut socket, &ServerMsg::Line { text: format!("blick: {err}") }).await;
            send(&mut socket, &ServerMsg::Done(RunResult::failed())).await;
            let _ = socket.send(Message::Close(None)).await;
            return;
        }
    };

    let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel();
    let run = run::run(&app.repo, &req.source, &req.flags, &tx);
    tokio::pin!(run);
    let result = loop {
        tokio::select! {
            result = &mut run => break result,
            Some(text) = rx.recv() => {
                // the page went away (closed or reloaded): dropping `run` stops it
                if !send(&mut socket, &ServerMsg::Line { text }).await {
                    return;
                }
            }
        }
    };
    while let Ok(text) = rx.try_recv() {
        if !send(&mut socket, &ServerMsg::Line { text }).await {
            return;
        }
    }
    let result = match result {
        Ok(result) => result,
        Err(err) => {
            send(&mut socket, &ServerMsg::Line { text: format!("blick: {err:#}") }).await;
            RunResult::failed()
        }
    };
    send(&mut socket, &ServerMsg::Done(result)).await;
    let _ = socket.send(Message::Close(None)).await;
}
