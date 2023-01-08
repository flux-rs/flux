#![feature(register_tool)]
#![register_tool(flux)]

// #[flux::sig(fn(x:i32) -> i32{v: v > x})]
// pub fn inc(x: i32) -> i32 {
//     x + 1
// }

#[flux::sig(fn(x:i32) -> i32[5])]
pub fn inc(_: i32) -> i32 {
    10 / 2
}
