#![feature(register_tool)]
#![register_tool(flux)]

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

#[flux::sig(fn() -> i32[1])]
pub fn test() -> i32 {
    let opt = MyOption::some(1);
    opt.unwrap()
}
