use flux_rs::*;

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

    #[sig(fn(usize{n: n < LIMIT}) -> usize)]
    pub fn repro(n: usize) -> usize {
        bounded(n)
    }
}
