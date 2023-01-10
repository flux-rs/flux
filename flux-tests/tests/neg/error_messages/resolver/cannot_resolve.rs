#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x:Vec<i32>) -> i32)] //~ ERROR cannot resolve
pub fn boo(x: i32) -> bool {
    x > 0
}
