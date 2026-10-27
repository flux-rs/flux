// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: requires crate::logic::nth_bit_set(n, 0)
// The replacement must retain the qualified logical function path.
mod logic {
    use flux_rs::*;

    defs! {
        fn nth_bit_set(bv: int, n: int) -> bool;
    }
}

mod target {
    use flux_rs::*;

    #[trusted]
    #[sig(fn(u32[@n]) -> u32 requires crate::logic::nth_bit_set(n, 0))]
    fn bounded(n: u32) -> u32 {
        n
    }

    #[sig(fn(u32) -> u32)]
    pub fn repro(n: u32) -> u32 {
        bounded(n) //~ ERROR refinement type error
    }
}
