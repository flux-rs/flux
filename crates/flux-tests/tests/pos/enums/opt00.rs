#[flux::refined_by(b:bool)]
pub enum Opt {
    #[flux::variant(Opt[false])]
    None,
    #[flux::variant(Opt[true])]
    Some,
}

#[flux::sig(fn(Opt[@b]) -> bool[b])]
pub fn is_some(x: Opt) -> bool {
    match x {
        Opt::None => false,
        Opt::Some => true,
    }
}

#[flux::sig(fn(Opt[@b]) -> bool[b])]
pub fn is_some_flip(x: Opt) -> bool {
    match x {
        Opt::Some => true,
        Opt::None => false,
    }
}

#[flux::sig(fn(i32{v:false}) -> T)]
pub fn never<T>(_x: i32) -> T {
    loop {}
}

#[flux::sig(fn(Opt[true]) -> i32)]
pub fn unwrap(x: Opt) -> i32 {
    match x {
        Opt::Some => 12,
        Opt::None => never(0),
    }
}
