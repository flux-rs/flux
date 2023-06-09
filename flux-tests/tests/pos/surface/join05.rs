#![feature(register_tool)]
#![register_tool(flux)]

struct S {
    f: i32,
}

#[flux::sig(fn(x: &strg S) ensures x: S)]
fn test(s: &mut S) {
    if true {
        s.f;
    }
    // *x should be correctly folded here
}
