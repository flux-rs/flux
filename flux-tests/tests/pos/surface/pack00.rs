#![feature(register_tool)]
#![register_tool(lr)]

fn bar() -> i32 {
    0
}

#[lr::sig(fn(bool) -> ())]
pub fn foo(b: bool) {
    let _x;
    if b {
    } else {
        _x = bar();
    }
}
