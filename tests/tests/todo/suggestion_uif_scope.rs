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

    #[sig(fn(u32{v: crate::logic::nth_bit_set(v, 0)}) -> u32)]
    pub fn repro(n: u32) -> u32 {
        bounded(n)
    }
}
