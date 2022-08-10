#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(b:bool)]
pub enum Opt {
    #[flux::variant(Opt[false])]
    None,
    #[flux::variant({i32} -> Opt[true])]
    Some(i32),
}

#[flux::sig(fn(Opt[@b]) -> bool[b])]
pub fn is_some(x: Opt) -> bool {
    match x {
        Opt::None => false,
        Opt::Some(_) => true,
    }
}

// #[flux::sig(fn(i32{v:false}) -> T)]
// pub fn never<T>(_x: i32) -> T {
//     loop {}
// }

// #[flux::sig(fn(Opt[true]) -> i32)]
// pub fn unwrap(x: Opt) -> i32 {
//     match x {
//         Opt::Some(val) => val,
//         _ => never(0),
//     }
// }

// #[flux::sig(fn() -> i32[12])]
// pub fn test() -> i32 {
//     let a = Opt::Some(12);
//     unwrap(a)
// }
