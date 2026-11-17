// Test that local qualifiers and axioms are resolved like other flux definitions: they are scoped
// to the module declaring them and can be named by a path or imported with `use`.

use flux_attrs::*;

#[spec(fn(bool[true]))]
fn assert(_b: bool) {}

pub mod hints {
    use flux_attrs::*;

    defs! {
        fn f(x: int) -> int;

        local axiom FPos(x: int) { f(x) > 0 }

        local qualifier Bound(x: int, y: int, z: int) { x + y <= z + 10 }
    }

    #[trusted]
    #[spec(fn(x: i32) -> i32[f(x)])]
    pub fn f(x: i32) -> i32 {
        x
    }

    // In the declaring module the bare name resolves
    #[axioms(FPos)]
    pub fn test_bare(x: i32) {
        super::assert(f(x) > 0);
    }

    pub mod nested {
        use flux_attrs::*;

        // `super::` paths work too
        #[axioms(super::FPos)]
        pub fn test_super(x: i32) {
            crate::assert(super::f(x) > 0);
        }
    }
}

// A qualified path
#[axioms(hints::FPos)]
pub fn test_path(x: i32) {
    assert(hints::f(x) > 0);
}

// An absolute path
#[axioms(crate::hints::FPos)]
pub fn test_crate_path(x: i32) {
    assert(hints::f(x) > 0);
}

mod imported {
    use flux_attrs::*;

    defs! {
        use crate::hints::FPos;
    }

    // An import with flux's `use`
    #[axioms(FPos)]
    pub fn test_use(x: i32) {
        crate::assert(crate::hints::f(x) > 0);
    }
}

// Two modules can declare local axioms with the same name
mod a {
    use flux_attrs::*;

    defs! {
        fn g(x: int) -> int;

        local axiom GPos(x: int) { g(x) > 0 }
    }

    #[trusted]
    #[spec(fn(x: i32) -> i32[g(x)])]
    pub fn g(x: i32) -> i32 {
        x
    }
}

mod b {
    use flux_attrs::*;

    defs! {
        fn g(x: int) -> int;

        local axiom GPos(x: int) { g(x) > 0 }
    }

    #[trusted]
    #[spec(fn(x: i32) -> i32[g(x)])]
    pub fn g(x: i32) -> i32 {
        x
    }
}

#[axioms(a::GPos, b::GPos)]
pub fn test_same_name(x: i32) {
    assert(a::g(x) > 0 && b::g(x) > 0);
}
