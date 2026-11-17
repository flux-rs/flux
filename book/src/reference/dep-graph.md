# Dependency Graphs

The `-Fdump-dep-graph` flag makes `flux` generate two dependency graphs for the local crate
or file being checked:

- `log/call_graph.json` — the **function call graph**: each node is a local function, and its
  `deps` are the other local functions it calls.
- `log/type_graph.json` — the **type dependency graph**: each node is a local struct or enum,
  and its `deps` are the other local types referenced in its field definitions.

Both files are JSON arrays of nodes, topologically sorted so that dependencies appear before
dependents (leaves first). Each node has the following fields:

| Field  | Type       | Description                                      |
|--------|------------|--------------------------------------------------|
| `uid`  | `number`   | Unique integer id (matches the array index)       |
| `path` | `string`   | The definition's path (e.g. `my_crate::foo::bar`) |
| `span` | `object`   | Source location (`file`, `start_line`, `start_col`, `end_line`, `end_col`) |
| `deps` | `number[]` | UIDs of the nodes this node depends on            |

`call_graph.json` has a single node per local function: a generic function and all the
instantiations at which it is called are merged into one node.

Usage:

```
cargo xtask run path/to/file.rs -- -Fdump-dep-graph
```

or

```
FLUXFLAGS="-Fdump-dep-graph" cargo flux check
```

or, in a `.flux/config.toml` file (see [`debug.dump-dep-graph`](config.md#debugdump-dep-graph)):

```toml
[debug]
dump-dep-graph = true
```
