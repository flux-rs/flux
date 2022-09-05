#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(b:bool)]
pub enum Opt<T> {
    #[flux::variant(Opt<T>[false])]
    None,
    #[flux::variant({T}-> Opt<T>[true])]
    Some(T),
}

#[flux::sig(fn(Opt<T>[@b]) -> bool[b])]
pub fn is_some<T>(x: Opt<T>) -> bool {
    match x {
        Opt::None => false,
        Opt::Some(_) => false,
    }
} //~ ERROR postcondition

#[flux::sig(fn(i32{v:false}) -> T)]
pub fn never<T>(_x: i32) -> T {
    loop {}
}

pub fn unwrap<T>(x: Opt<T>) -> T {
    match x {
        Opt::Some(v) => v,
        Opt::None => never(0), //~ ERROR precondition
    }
}
