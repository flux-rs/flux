#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(b:bool)]
pub enum Opt<T> {
    #[flux::variant(Opt<T>[false])]
    None,
    #[flux::variant(Opt<T>[true])]
    Some(T),
}

#[flux::sig(fn(Opt<i32>[true]) -> i32)]
pub fn unwrap_i32(x: Opt<i32>) -> i32 {
    match x {
        Opt::Some(v) => v,
        Opt::None => 0,
    }
}
