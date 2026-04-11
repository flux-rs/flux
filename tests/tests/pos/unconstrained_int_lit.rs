// Check that we fallback to `int` for unconstrained integer literals

use flux_attrs::*;

defs! {
    fn test() -> bool {
        42 <= 42
    }
}
