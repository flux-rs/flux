#![feature(register_tool, box_patterns)]
#![register_tool(flux)]

enum E {
    #[flux::variant((i32{v: v >= 0}) -> E)]
    A(i32),
}

#[flux::sig(fn(E) -> i32{v : v > 0})]
fn foo(e: E) -> i32 {
    match e {
        E::A(x) => x + 1,
    }
}
