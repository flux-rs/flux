#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x:i32, y: i32{x != y}))]
pub fn ipa(x: i32, y: i32) {}

pub fn ris() {
    ipa(0, 1);
}
