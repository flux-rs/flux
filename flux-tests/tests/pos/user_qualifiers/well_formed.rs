#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::qualifier(MyQ1(x: int, a: int) { x == a })]
#![flux::qualifier(MyQ2(x: int) { x > 1 })]

#[flux::sig(fn(i32[@n]) -> i32[n])]
pub fn dummy(x: i32) -> i32 {
    x
}
