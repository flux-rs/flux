pub mod defs {
    use flux_attrs::*;

    defs! {
        #[hide]
        fn foo(n: int) -> bool {
            n > 0
        }

        local axiom FooPos(n: int) { foo(n) }
    }

    pub mod nested {
        // Like other items, function definitions are not visible across a module boundary
        #[flux_attrs::reveal(foo)] //~ ERROR unknown function definition
        pub fn test00() {}
    }
}

#[flux::reveal(defs::fool)] //~ ERROR unknown function definition
pub fn test01() {}

#[flux::reveal(defs::FooPos)] //~ ERROR unknown function definition
pub fn test02() {}

#[flux::hide(nope::foo)] //~ ERROR unknown function definition
pub fn test03() {}
