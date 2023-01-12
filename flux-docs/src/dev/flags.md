# Command Line Flags

You can set various `env` variables to customize the behavior of `flux`.

* `FLUX_CONFIG` tells `flux` where to find a config file for these settings.
  - By default, `flux` searches its directory for a `flux.toml` or `.flux.toml`.
* `FLUX_PATH=path/to/flux` tells `cargo-flux` and `rustc-flux` where to find the `flux` binary. 
  - Defaults to the default `flux` installation (typically found in `~/.cargo/bin`).
* `FLUX_LOG_DIR=path/to/log/`  with default `./log/`
* `FLUX_DUMP_CONSTRAINT=1` sets the directory where constraints, timing and cache are saved.
* `FLUX_DUMP_CHECKER_TRACE=1` saves the checker's trace (useful for debugging!)
* `FLUX_DUMP_TIMINGS=1` saves the profile information
* `FLUX_DUMP_MIR=1` saves the low-level MIR for each analyzed function
* `FLUX_CHECK_ASSERTS={ignore, assume, check}` TODO
* `FLUX_POINTER_WIDTH=N` TODO (default `64`)
* `FLUX_CHECK_DEF=name` only checks definitions containing `name` as a substring
* `FLUX_CACHE=1"` switches on query caching and saves the cache in `FLUX_CACHE_FILE`
* `FLUX_CACHE_FILE=file.json` customizes the cache file, default `FLUX_LOG_DIR/cache.json`

# Config file

The config file is a `.toml` file that just contains on each line the lowercase
name of a `flux` command line flag without the `FLUX_` prefix. Set environment
variables take priority over the config file.

The config file should be in the project root.

For example, suppose your project root contains the following `flux.toml`.

```toml
log_dir = "./test"
dump_timings = true
dump_mir = true
```

and you run in the project root

```bash
FLUX_DUMP_MIR=0 cargo-flux check
```

then `flux` will create the directory `./test/` and write `./test/timings`, a file
containing profiling information. It will _not_ dump the MIR because that setting
was overriden by setting `FLUX_DUMP_MIR=0`.

## Check Asserts

TODO

## Query Caching

`LR_CACHE=1` persistently caches the safe fixpoint queries for each DefId
in `LR_LOG_DIR/LR_CACHE_FILE`, and on subsequent runs, skips queries that
are already in the cache, which considerably speeds up `cargo-flux check`
on an entire crate.
