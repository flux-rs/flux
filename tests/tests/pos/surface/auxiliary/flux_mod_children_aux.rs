use flux_attrs::*;

defs! {
    fn root_shift(x: int) -> int { x + 2 }
}

pub mod mod_a {
    use flux_attrs::*;

    defs! {
        fn shift(x: int) -> int { x + 1 }
    }

    // A second `defs!` in the same module
    defs! {
        fn shift_again(x: int) -> int { x + 1 }
    }

    pub mod nested {
        use flux_attrs::*;

        defs! {
            fn nested_shift(x: int) -> int { x + 3 }
        }
    }
}
