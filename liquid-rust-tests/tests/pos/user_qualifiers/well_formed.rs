#![feature(register_tool)]
#![register_tool(lr)]
#![feature(custom_inner_attributes)]
#![lr::qualifier(MyQ1(x: int, a: int) -> x == a)]
#![lr::qualifier(MyQ2(x: int) -> x > 1)]

#[lr::sig(fn(i32[@n]) -> i32[n])]
pub fn dummy(x: i32) -> i32 {
    x
}
