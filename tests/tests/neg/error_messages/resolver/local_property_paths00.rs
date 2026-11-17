use flux_attrs::*;

pub mod props {
    use flux_attrs::*;

    defs! {
        fn f(x: int) -> int;

        local property ShiftByTwo[<<](x, y) {
            [<<](x, 2) == 4*x
        }

        local axiom FPos(x: int) { f(x) > 0 }
    }

    pub mod nested {
        use flux_attrs::*;

        // Like other items, properties are not visible across a module boundary by their bare name
        #[properties(ShiftByTwo)] //~ ERROR unknown property
        pub fn test00() {}
    }
}

#[properties(props::Nope)] //~ ERROR unknown property
pub fn test01() {}

#[properties(props::FPos)] //~ ERROR unknown property
pub fn test02() {}

#[axioms(props::ShiftByTwo)] //~ ERROR unknown axiom
pub fn test03() {}
