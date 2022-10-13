#![feature(register_tool, custom_inner_attributes)]
#![register_tool(flux)]

#[flux::sig(fn(a: i32, b: i32) -> i32[if a < b { a } else { b }])]
pub fn min(a: i32, b: i32) -> i32 {
    if a <= b {
        a
    } else {
        b
    }
}
