#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x: i32, y: i32{y == -x}))]
pub fn test00(x: i32, y: i32) {}

pub fn test01() {
    test00(1, -1);
}
