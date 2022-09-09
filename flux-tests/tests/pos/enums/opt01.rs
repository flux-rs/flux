#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(b:bool)]
pub enum Opt<T> {
    #[flux::variant(Opt<T>[false])]
    None,
    #[flux::variant({T} -> Opt<T>[true])]
    Some(T),
}

#[flux::sig(fn(Opt<T>[@b]) -> bool[b])]
pub fn is_some<T>(x: Opt<T>) -> bool {
    match x {
        Opt::None => false,
        Opt::Some(_) => true,
    }
}

#[flux::sig(fn(Opt<T>[@b]) -> bool[b])]
pub fn is_some_flip<T>(x: Opt<T>) -> bool {
    match x {
        Opt::Some(_) => true,
        Opt::None => false,
    }
}

#[flux::sig(fn(i32{v:false}) -> T)]
pub fn never<T>(_x: i32) -> T {
    loop {}
}

#[flux::sig(fn(Opt<T>[true]) -> T)]
pub fn unwrap<T>(x: Opt<T>) -> T {
    match x {
        Opt::Some(v) => v,
<<<<<<< HEAD
        Opt::None => unwrap(x),
=======
        Opt::None => never(0),
>>>>>>> 2366c608d420f4410e1bacd556040db15008cc14
    }
}
