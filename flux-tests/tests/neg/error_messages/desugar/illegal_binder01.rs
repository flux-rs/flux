#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(Option<i32[@n]>) -> i32[n+1])] //~ ERROR illegal binder
pub fn inc(b: Option<i32>) -> i32 {
    if b.is_some() {
        let n = b.unwrap();
        n + 1
    } else {
        loop {}
    }
}

pub fn inc_test(n: i32) -> i32 {
    let b0 = Option::Some(n);
    inc(b0)
}
