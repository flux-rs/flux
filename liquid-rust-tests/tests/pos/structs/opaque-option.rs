#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/surface/my_option.rs"]
mod my_option;
use my_option::MyOption;

pub fn unwrap_or_else<T>(opt: MyOption<T>, val: T) -> T {
    if opt.is_some() {
        opt.unwrap()
    } else {
        val
    }
}

#[lr::sig(fn() -> i32[1])]
pub fn test() -> i32 {
    let opt = MyOption::some(1);
    opt.unwrap()
}

#[lr::assume]
#[lr::sig(fn(T) -> Option<T>)]
fn some<T>(x: T) -> Option<T> {
    Option::Some(x)
}

#[lr::assume]
#[lr::sig(fn(Option<T>) -> T)]
fn unwrap<T>(x: Option<T>) -> T {
    match x {
        Some(v) => v,
        None => panic!("ohh"),
    }
}

#[lr::sig(fn() -> i32[1])]
pub fn test2() -> i32 {
    let opt = some(1);
    opt.unwrap()
}
