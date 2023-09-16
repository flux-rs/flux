#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(_) -> Option<_>)]
fn test00(x: i32) -> Option<i32> {
    Some(x)
}

#[flux::sig(fn(x: &strg _) ensures x: i32[0])]
fn test01(x: &mut i32) {
    *x = 0;
}

#[flux::sig(fn(x: &strg i32) ensures x: _)]
fn test02(x: &mut i32) {
    *x = 0;
}
