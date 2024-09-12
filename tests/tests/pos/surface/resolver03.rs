// Allow paths in sorts

mod mod_a {
    use flux_rs::*;

    defs! {
        fn add1(x: crate::mod_b::S) -> int {
            x.n + 1
        }
    }
}

mod mod_b {
    use flux_rs::*;

    #[opaque]
    #[refined_by(n: int)]
    pub struct S;
}
