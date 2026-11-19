// Talking to the blick server (see `src/main.rs` in the crate).

import type { FileList } from "./bindings/FileList";
import type { Info } from "./bindings/Info";
import type { RunRequest } from "./bindings/RunRequest";
import type { RunResult } from "./bindings/RunResult";
import type { ServerMsg } from "./bindings/ServerMsg";

const wsUrl = (path: string) => `${location.protocol === "https:" ? "wss" : "ws"}://${location.host}${path}`;

export async function fetchInfo(): Promise<Info> {
  const r = await fetch("/api/info");
  return r.json();
}

async function ok(r: Response): Promise<Response> {
  if (!r.ok) throw new Error((await r.text()) || `${r.status} ${r.statusText}`);
  return r;
}

/** The programs the page can open: the `.rs` files of the folder blick was started with. */
export async function fetchFiles(): Promise<FileList> {
  return (await ok(await fetch("/api/files"))).json();
}

/** The contents of `path`, relative to the folder of `fetchFiles`. */
export async function fetchFile(path: string): Promise<string> {
  return (await ok(await fetch(`/api/file/${path.split("/").map(encodeURIComponent).join("/")}`))).text();
}

/**
 * Runs Flux over the WebSocket: `onLine` gets every output line as `cargo x run` prints it;
 * resolves with the final result.
 */
export function runOverSocket(req: RunRequest, onLine: (line: string) => void): Promise<RunResult> {
  return new Promise((resolve, reject) => {
    const ws = new WebSocket(wsUrl("/api/run-ws"));
    let done = false;
    ws.onopen = () => ws.send(JSON.stringify(req));
    ws.onmessage = e => {
      const m: ServerMsg = JSON.parse(e.data);
      if (m.type === "line") onLine(m.text);
      else if (m.type === "done") {
        done = true;
        resolve(m);
        ws.close();
      }
    };
    ws.onerror = () => {
      if (!done) reject(new Error("connection to the server failed"));
    };
    ws.onclose = () => {
      if (!done) reject(new Error("the server closed the connection before the run finished"));
    };
  });
}

/**
 * Reloads the page when the server says the client was rebuilt, and when the server comes back
 * after a restart (it may serve a newer client).
 */
export function watchReload() {
  let lost = false;
  const connect = () => {
    const ws = new WebSocket(wsUrl("/api/reload"));
    ws.onopen = () => {
      if (lost) location.reload();
    };
    ws.onmessage = () => location.reload();
    ws.onclose = () => {
      lost = true;
      setTimeout(connect, 1000);
    };
  };
  connect();
}
