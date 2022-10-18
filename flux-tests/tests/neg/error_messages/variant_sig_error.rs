#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(b:bool)]
pub enum Opt<T> {
    #[flux::variant(Opt<T>[false])]
    None,
    #[flux::variant(Opt<T>[true])] //~ ERROR field count mismatch
    Some(T),
}

#[flux::sig(fn(Opt<i32>[true]) -> i32)]
pub fn unwrap_i32(x: Opt<i32>) -> i32 {
    match x {
        Opt::Some(v) => v,
        Opt::None => 0,
    }
}

#[flux::refined_by(b:bool)]
pub enum E1<T> {
    #[flux::variant(Opt<T>[false])] //~ ERROR cannot resolve
    A,
    #[flux::variant({T} -> Opt<T>[true])] //~ ERROR cannot resolve
    B(T),
}

#[flux::refined_by(b: int)]
pub enum E2 {
    #[flux::variant((i32[true]) -> E2[0])] //~ ERROR mismatched sorts
    A(i32),
    #[flux::variant(E2[true])] //~ ERROR mismatched sorts
    B,
    #[flux::variant((i32[@n]) -> E2[@n])] //~ ERROR illegal binder
    C(i32),
}
