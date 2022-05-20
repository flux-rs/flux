#![feature(register_tool)]
#![register_tool(lr)]

fn bar() -> i32 {
    0
}

#[lr::sig(fn(bool) -> ())]
fn foo(b: bool) {
    let x;
    if b {
    } else {
        x = bar();
    }
}
