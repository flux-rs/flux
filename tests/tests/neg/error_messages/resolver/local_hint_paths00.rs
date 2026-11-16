use flux_attrs::*;

pub mod hints {
    use flux_attrs::*;

    defs! {
        fn f(x: int) -> int;

        local axiom FPos(x: int) { f(x) > 0 }

        local qualifier Bound(x: int, y: int) { x <= y }
    }

    pub mod nested {
        use flux_attrs::*;

        // Like other items, hints are not visible across a module boundary by their bare name
        #[axioms(FPos)] //~ ERROR unknown axiom
        pub fn test00() {}

        #[qualifiers(Bound)] //~ ERROR unknown qualifier
        pub fn test01() {}
    }
}

#[axioms(hints::Nope)] //~ ERROR unknown axiom
pub fn test02() {}

#[axioms(hints::Bound)] //~ ERROR unknown axiom
pub fn test03() {}

#[qualifiers(hints::FPos)] //~ ERROR unknown qualifier
pub fn test04() {}

#[axioms(hints::f)] //~ ERROR unknown axiom
pub fn test05() {}
