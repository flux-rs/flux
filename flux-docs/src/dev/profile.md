# Profiling Flux

Set `FLUX_DUMP_TIMINGS=true` to have flux write timing diagnostics to `./log/timings`.

Right now this is _extremely_ simple, it just provides some details for the spans under `flux_typeck` and `flux_driver`.

## Sample output

Below is a sample output for an invocation of `cargo-flux check` that took 19 seconds. The missing 2 seconds approximately accounts for the time it takes for `cargo check` to run.

Note that `check_crate` contains everything running under `check_top`, which is why the sum of the spans is greater than 19 seconds.

```
check_top
  Checker::infer
    num events:   205
    min non-zero: 0.52ms
    1st quartile: 0.52ms
    2nd quartile: 1.05ms
    3rd quartile: 2.62ms
    max:          24.12ms
    total time:   229.64ms
  Checker::check
    num events:   205
    min non-zero: 0.52ms
    1st quartile: 0.52ms
    2nd quartile: 1.05ms
    3rd quartile: 5.24ms
    max:          159.91ms
    total time:   2028.47ms
  FixpointCtx::check
    num events:   205
    min non-zero: 22.02ms
    1st quartile: 26.21ms
    2nd quartile: 28.31ms
    3rd quartile: 40.37ms
    max:          1867.51ms
    total time:   9106.36ms
total time: 11364.47ms

check_crate
  Callbacks::check_wf
    num events:   1
    min non-zero: 18.35ms
    1st quartile: 18.87ms
    2nd quartile: 18.87ms
    3rd quartile: 18.87ms
    max:          18.87ms
    total time:   18.87ms
  Callbacks::check_crate
    num events:   1
    min non-zero: 16986.93ms
    1st quartile: 16995.32ms
    2nd quartile: 16995.32ms
    3rd quartile: 16995.32ms
    max:          16995.32ms
    total time:   16995.32ms
total time: 17014.19ms
```
