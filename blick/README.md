# blick

Run Flux on programs and watch its refinement checker work, in the browser.

> **blick** /blɪk/ *noun*
>
> The flash of light from a bead of silver or gold at the end of
> [cupellation](https://en.wikipedia.org/wiki/Cupellation), which tells the assayer the metal is
> refined.

## Running

```
cargo run -p blick [-- --port 8765]
```

Then open http://127.0.0.1:8765. It needs Node.js and npm: on startup it installs the client's
packages when they are missing or out of date (`npm ci`) and runs `vite build --watch` on the
client, so edits to `client/` show up in the page, which reloads after each rebuild.

## Layout

- `src/`: the server (axum). A run writes the program to a temporary file and runs
  `cargo x run <file> -- -Fdump-checker-trace=debug` from the repository root, streaming its
  output to the page over a WebSocket.
- `client/`: the page (React, TypeScript, Vite). `client/src/bindings` holds the TypeScript types
  of the server's messages, generated from `src/protocol.rs` on startup.

To add a client package: `npm install <pkg>` in `client/`, and commit `package-lock.json`.
To type-check the client: `npm run check` in `client/`.
