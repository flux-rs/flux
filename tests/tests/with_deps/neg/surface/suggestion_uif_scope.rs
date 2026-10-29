// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 4
// suggestion: requires crate::logic::nth_bit_set(n, 0)
// suggestion: requires crate::logic::other_pred(n)
// suggestion: requires crate::root_pred(n)
// suggestion: requires crate::attr_logic::attr_pred(n)
// The replacement must retain the qualified logical function path.
flux_rs::defs! {
    fn root_pred(n: int) -> bool;
}

mod logic {
    use flux_rs::*;

    defs! {
        fn nth_bit_set(bv: int, n: int) -> bool;
    }

    // A later wrapper has a different disambiguator, but no source path component.
    defs! {
        fn other_pred(n: int) -> bool;
    }
}

mod attr_logic {
    #![flux::defs {
        fn attr_pred(n: int) -> bool;
    }]
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

    #[trusted]
    #[sig(fn(u32[@n]) -> u32 requires crate::logic::other_pred(n))]
    fn bounded_other(n: u32) -> u32 {
        n
    }

    #[sig(fn(u32) -> u32)]
    pub fn repro_other(n: u32) -> u32 {
        bounded_other(n) //~ ERROR refinement type error
    }

    #[trusted]
    #[sig(fn(u32[@n]) -> u32 requires crate::root_pred(n))]
    fn bounded_root(n: u32) -> u32 {
        n
    }

    #[sig(fn(u32) -> u32)]
    pub fn repro_root(n: u32) -> u32 {
        bounded_root(n) //~ ERROR refinement type error
    }

    #[trusted]
    #[sig(fn(u32[@n]) -> u32 requires crate::attr_logic::attr_pred(n))]
    fn bounded_attr(n: u32) -> u32 {
        n
    }

    #[sig(fn(u32) -> u32)]
    pub fn repro_attr(n: u32) -> u32 {
        bounded_attr(n) //~ ERROR refinement type error
    }
}
