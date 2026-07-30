mod mod_a {
    use flux_attrs::*;

    defs! {
        fn shift(x: int) -> int { x + 1 }
    }
}

mod mod_b {
    // `shift` is only defined in `mod_a`, so it cannot be referred to from `mod_b`
    #[flux::sig(fn(x: i32) -> i32[mod_b::shift(x)])] //~ ERROR cannot find value
    pub fn test(x: i32) -> i32 {
        x + 1
    }
}
