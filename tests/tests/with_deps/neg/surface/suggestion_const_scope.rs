// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: requires n < crate::types::LIMIT
// The replacement must keep LIMIT resolvable from target.

mod types {
    pub const LIMIT: usize = 1024;
}

mod target {
    use crate::types::*;
    use flux_rs::*;

    #[trusted]
    #[sig(fn(usize{n: n < LIMIT}) -> usize)]
    fn bounded(n: usize) -> usize {
        n
    }

    #[sig(fn(usize) -> usize)]
    pub fn repro(n: usize) -> usize {
        bounded(n) //~ ERROR refinement type error
    }
}
