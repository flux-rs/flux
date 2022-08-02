#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/my_option.rs"]
mod my_option;
use my_option::MyOption;

#[flux::sig(fn(MyOption<i32[@n]>) -> i32[n+1])] //~ ERROR illegal binder
pub fn inc(b: MyOption<i32>) -> i32 {
    if b.is_some() {
        let n = b.unwrap();
        n + 1
    } else {
        loop {}
    }
}

pub fn inc_test(n: i32) -> i32 {
    let b0 = MyOption::some(n);
    inc(b0)
}
