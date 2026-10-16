// Flux definitions cannot mention the generic parameters or `Self` of the enclosing item

use flux_attrs::*;

pub struct Bar<T>(T);

impl<T> Bar<T> {
    pub fn foo() {
        defs! {
            fn f() -> int {
                <Self as Sized>::size_of() //~ ERROR can't use generic parameters from outer item
            }
        }
    }
}

pub struct Baz;

impl Baz {
    pub fn foo() {
        defs! {
            fn f() -> int {
                <Self as Sized>::size_of() //~ ERROR can't use generic parameters from outer item
            }
        }
    }
}

pub fn foo<T>() {
    defs! {
        fn f() -> int {
            <T as Sized>::size_of() //~ ERROR can't use generic parameters from outer item
        }
    }
}

pub fn bar<const N: usize>() {
    defs! {
        fn f() -> int {
            <[i32; N] as Sized>::size_of() //~ ERROR can't use generic parameters from outer item
        }
    }
}

pub fn baz<const N: usize>() {
    defs! {
        fn f() -> int {
            N //~ ERROR can't use generic parameters from outer item
        }
    }
}

pub fn qux<T>() {
    defs! {
        fn f(x: T) -> int { //~ ERROR can't use generic parameters from outer item
            0
        }
    }
}

#[flux::refined_by(n: int)]
pub struct Quux {
    #[flux::field(i32[n])]
    x: i32,
}

impl Quux {
    pub fn foo() {
        defs! {
            fn f(x: Self) -> int { //~ ERROR can't use generic parameters from outer item
                x.n
            }
        }
    }
}

pub trait Tr {
    fn foo() {
        defs! {
            fn f() -> int {
                <Self as Sized>::size_of() //~ ERROR can't use generic parameters from outer item
            }
        }
    }
}
