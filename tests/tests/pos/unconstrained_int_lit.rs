// Check that we fallback to `int` for unconstrained integer literals

use flux_rs::attrs::*;

defs! {
    fn test() -> bool {
        42 <= 42
    }
}
