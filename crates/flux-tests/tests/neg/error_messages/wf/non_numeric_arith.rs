#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(b: bool) -> i32[b + 0])] //~ ERROR mismatched sorts
fn test00(b: bool) -> i32 {
    todo!()
}

#[flux::sig(fn(b: bool) -> i32[0 + b])] //~ ERROR mismatched sorts
fn test01(b: bool) -> i32 {
    todo!()
}

#[flux::sig(fn(b: bool) -> bool[b < 0])] //~ ERROR mismatched sorts
fn test02(b: bool) -> bool {
    todo!()
}
