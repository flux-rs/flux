# Command Line Flags

You can set various `env` variables to customize the behavior of `flux`.

* `LR_LOG_DIR=path/to/log/`  with default `./log/`
* `LR_DUMP_CONSTRAINT=1` sets the directory where constraints, timing and cache are saved.
* `LR_DUMP_CHECKER_TRACE=1` saves the checker's trace (useful for debugging!)
* `LR_DUMP_TIMINGS=1` saves the profile information
* `LR_DUMP_MIR=1` saves the low-level MIR for each analyzed function
* `LR_CHECK_ASSERTS={ignore, assume, check}` TODO
* `LR_POINTER_WIDTH=N` TODO (default `64`)
* `LR_CHECK_DEF=name` only checks definitions containing `name` as a substring
* `LR_CACHE=1"` switches on query caching and saves the cache in `LR_CACHE_FILE`
* `LR_CACHE_FILE=file.json` customizes the cache file, default `LR_LOG_DIR/cache.json`

## Check Asserts

TODO

## Query Caching

`LR_CACHE=1` persistently caches the safe fixpoint queries for each DefId
in `LR_LOG_DIR/LR_CACHE_FILE`, and on subsequent runs, skips queries that
are already in the cache, which considerably speeds up `cargo-flux check`
on an entire crate.