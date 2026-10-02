// Primitive Rust types use the same fallback in specifications.
mod i32 {
    pub type Member = bool;
    pub const MIN: i32 = 0;
}

#[flux::spec(fn(x: i32) -> i32[x])]
fn identity_i32(x: i32) -> i32 {
    x
}

// A missing module member can resolve to a primitive's associated constant.
#[flux::spec(fn() -> i32[i32::MAX])]
fn max() -> i32 {
    i32::MAX
}

// A successfully resolved module member still wins.
#[flux::spec(fn(x: i32::Member) -> bool[x])]
fn member(x: i32::Member) -> bool {
    x
}

// A type alias shadows a primitive type.
mod alias {
    type A = bool;
    use A as i32;

    #[flux::spec(fn(x: i32) -> bool[x])]
    fn identity(x: i32) -> bool {
        x
    }
}

// Look in Rust's value namespace before falling back to the primitive.
#[flux::spec(fn() -> i32[i32::MIN])]
fn module_constant() -> i32 {
    0
}

mod int {
    pub struct S;
}

// An import path must resolve to the module, not the builtin sort.
use int::*;

#[flux::spec(fn(x: S) -> S)]
fn imported(x: S) -> S {
    x
}
